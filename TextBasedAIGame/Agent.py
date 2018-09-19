#!/usr/bin/env python3
# agent.py


# Data structures:
# This agent will convert message from Raft into a coordinate tuple(x,y),
# these coordinates are stored in a dictionary names map_dict,
# the value of key is str likes ' ','k' and so on.
# When agent move to a position contains items like key, axe, treasure and so on
# different items location will be store in seperate sets.
# Then we initialize boolean variables as agent status to determine whether agent
# has items or not.
# When agent is computing paths to target locations, a list() is used for storing sequences
# of positions(coordinates).
#
# Main design:
# The major logic decision of agent is written in (def make_decision),
# which encourges agent to go back to start position as first priority if treasure has been found.
# Otherwise, agent will explore map to get more information to win the game. on land.
# After unreachable positions have been visited, agent will go for get items and try to figure out
# a path to get treasure.
# At this point, by computing a none way to get treasure, agent is allowed use boat(if it can by checking
# agent.have_boat) to explore sea.
# After agent finished exploration, there are more items information have been stored.
# Agent will find paths for each items and go for it.
# It is worth metnioning that when agent on the boat and it is looking for a item on land area, the cost of
# walking in the land will be increased in order to limited the times of landing.
# The priority of cutting tree is lower than either getting key, gettig bombs, therefore the situation of 
# tring to go ashore and cut a tree from sea location will never happen except this is the only choice.
# After exploration of sea, if agent still can not get treasure and go back home. It will explore other lands or sea,
# and continue steps above.
# 
#
# Algorithm:
# A star search algorithm is mainly used in (def path_find), current_position and target as two parameters will be transfer
# into path_find function, detail explannation is commented in that function.
#
import socket
import sys
from io import StringIO
import copy
import random

socket_ip = "localhost"
socket_port = int(sys.argv[2])
Clientsocket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
try:
    Clientsocket.connect((socket_ip, socket_port))
    messg = Clientsocket.makefile('r')
except:
    print('Server not online')
    sys.exit()


class Agent:
    def __init__(self):
        self.x = 0
        self.y = 0
        #       rule = {('S', 'l'): 'E', ('S', 'r'): 'W',
        #              ('E', 'l'): 'N', ('E', 'r'): 'S',
        #              ('N', 'l'): 'W', ('N', 'r'): 'E',
        #              ('W', 'l'): 'S', ('W', 'r'): 'N'}
        # direction: E:0 S:1 W:2 N:3
        # self.direction = "S"
        self.direction = 1
        self.map = Map()
        self.have_key = False
        self.have_axe = False
        self.have_boat = False
        self.on_boat = False
        self.sail_allowed= False
        self.have_dynamite = 0
        self.have_gold = False
        self.item = {'u': '-', 'c': 'T', 'b': ('*', 'T')}
        self.path_find_visited = set()
        self.dynamite_locations = set()
        self.axe_locations = set()
        self.key_locations = set()
        self.tree_locations = set()
        self.treasure_location = None
        self.random_walk = True
        self.unvisited_location = set()
        self.cannot_visited_location = set()
        self.visited_location =set()
        self.exploring_target = None
        self.cost_dict = {}
        self.heuristic_dict ={}
        self.parent_dict = {}
        self.sea_locations = set()
        self.visited_sea_location = set()
        self.unvisited_sea_location = set()
        self.exploring_sea_target = None
        self.got_treasure=False
        self.explore_sea=False
        self.cannot_visited_sea = set()
        self.wall_locations = set()
        self.final_situation = False
        self.boom_list =set()
        #self.bomb_path = set()
        
    def random_explore_sea(self):
        #Store current_location into visited_sea_location.
        #When agent starts its sea exploretion on land, allows agent use boat. 
        self.sail_allowed = True
        current_location = self.x, self.y
        self.visited_sea_location.add(current_location)
        self.unvisited_sea_location -= self.visited_sea_location
        #If agent reachs target position, resets target position.
        if current_location == self.exploring_sea_target:
            self.exploring_sea_target = None
        #If agent has none target position, search in the map.
        #Update unvisited_location and unvisited_sea_location.
        if not self.exploring_sea_target:
            for loc in self.map.map_dict:
                if loc not in self.sea_locations:
                    self.unvisited_location.add(loc)
                elif loc not in self.visited_sea_location:
                    self.unvisited_sea_location.add(loc)
            #While loop for search a reachable target position.
            while True:
                if not self.unvisited_sea_location:
                    break
                #Continuely pick target which has the lowest cost between current_location and target position.
                self.exploring_sea_target = sorted(self.unvisited_sea_location, key=lambda sea_node: (
                self.get_cost(current_location, (sea_node[0], sea_node[1]))))[0]
                path = self.path_find(self.exploring_sea_target)
                if path:
                    break
                else:
                    #If unreachable, add it into cannot_visited_sea.
                    self.cannot_visited_sea.add(self.exploring_sea_target)
                    self.unvisited_sea_location -= self.cannot_visited_sea
            #If agent has explored current sea area completely, end this function.
            if not self.unvisited_sea_location:
                self.explore_sea= False
                self.boom_list = set()
                return
            action = self.path_to_output(path)
            return action
        #If agent has been set a target position, continue the movements.
        else:
            path = self.path_find(self.exploring_sea_target)
            if not self.unvisited_sea_location:
                self.explore_sea = False
                self.boom_list = set()
                return
            action = self.path_to_output(path)
            return action

    def random_explore(self):
        #Store current_location to visited_location.
        current_location = self.x,self.y
        self.visited_location.add(current_location)
        self.unvisited_location -= self.visited_location
        #If agent reachs target position, resets target position.
        if current_location == self.exploring_target:
            self.exploring_target = None
        #If agent has none target position, search in the map.
        #Update unvisited_location and unvisited_sea_location.
        if not self.exploring_target:
            for loc in self.map.map_dict:
                if self.map.map_dict[loc] == '~' and loc not in self.visited_sea_location:
                    self.unvisited_sea_location.add(loc)
                if self.map.map_dict[loc] == "d":
                        self.boom_list.add(loc)
                elif loc not in self.visited_location:
                    self.unvisited_location.add(loc)
            #While loop for search a reachable target position.
            while True:
                if not self.unvisited_location:
                    break
                #Continuely pick target which has the lowest cost between current_location and target position.
                self.exploring_target = sorted(self.unvisited_location, key=lambda node:(self.get_cost(current_location,(node[0],node[1]))))[0]
                path = self.path_find(self.exploring_target)
                if path:
                    break
                else:
                #If unreachable, add it into cannot_visited_location.
                    self.cannot_visited_location.add(self.exploring_target)
                    self.unvisited_location -= self.cannot_visited_location
            #If agent has explored current land area completely, end this function.
            if not self.unvisited_location:
                self.random_walk = False
                return
            action = self.path_to_output(path)
            return action
        #If agent has been set a target position, continue the movements.
        else:
            path = self.path_find(self.exploring_target)
            if not self.unvisited_location:
                self.random_walk = False
                return
            action = self.path_to_output(path)
            return action

    def make_decision(self):
        
        #If agent got treasure, it should figure out the path to start point.
        #If there is a valid path, go back to start point.
        if self.got_treasure:
            path = self.path_find((0,0))
            if path:
                return self.path_to_output(path)
        #If agent have no treasure, it should explore the land area as much as it can.
        if self.random_walk:
            action=self.random_explore()
            if action:
                return action
        #If agent has received dynamites location, computes a path to dynamites.
        #If there are valid paths, go and pick them.
        if self.dynamite_locations:
            for loc in self.dynamite_locations:
                path = self.path_find(loc)
                if path:
                    return self.path_to_output(path)
        #At the time agent can not find items any more, if agent have boat or it on boat.
        if (self.have_boat or self.on_boat) and not self.random_walk:
            self.explore_sea=True
            action = self.random_explore_sea()
            if action:
                return action
        #If agent has received treasure location, computes the path to treasure.
        #If there is a vaild path, go and pick treasure.
        if self.treasure_location:
            path = self.path_find(self.treasure_location)
            if path:
                return self.path_to_output(path)
        #If agent has none axe and receive axe location, computes a path to axe.
        #If there is a vaild path, go and pick axe.
        if (not self.have_axe) and self.axe_locations:
            for loc in self.axe_locations:
                path = self.path_find(loc)
                if path:
                    return self.path_to_output(path)
        #If agent has received key location and has none key, computes a path to key.
        #If there is a valid path, go and pick them.
        if (not self.have_key) and self.key_locations:
            for loc in self.key_locations:
                path = self.path_find(loc)
                if path:
                    return self.path_to_output(path)
        #If agent does have a boat but it has axe, compute a path to a tree nearest to agent.
        #If there is a valid path, go for it.
        if (not self.have_boat) and self.have_axe:
            for loc in sorted(self.tree_locations,key=lambda loc:self.get_cost((self.x,self.y),loc)):
                #Find a nearest tree.
                path = self.path_find(loc)
                if path:
                    return self.path_to_output(path)
        #If there are none choice for next decision, agent is allowed random explore land area to continue
        #selections above.
        if not (self.random_walk and self.explore_sea):
            self.random_walk=True
            return self.random_explore()
        #print("Error. No decision.")

    #By the way, empty_block_symbols is list of items that agent could walk through on specific conditions.
    def get_neighbours(self, current):
        x, y = current
        neighbours = [(x + 1, y), (x, y + 1), (x - 1, y), (x, y - 1)]
        available_neighbours = []
        empty_block_symbols = [' ', 'd', 'k', 'a','$']
        if self.have_axe:
            empty_block_symbols += ['T']
        if self.have_key:
            empty_block_symbols += ['-']
        if self.have_boat or self.on_boat:
            empty_block_symbols += ['~']
        if self.have_dynamite:
            empty_block_symbols+=['*']
        for move in neighbours:
            if move in self.map.map_dict and move not in self.path_find_visited and self.map.map_dict[move] \
                    in empty_block_symbols:
                if not (self.map.map_dict[current]=='~' and self.map.map_dict[move] in ['*','T']):
                    available_neighbours.append(move)
        return available_neighbours

    def random_sail_get_neighbours(self, current):
        x, y = current
        neighbours = [(x + 1, y), (x, y + 1), (x - 1, y), (x, y - 1)]
        available_neighbours = []
        empty_block_symbols = ['~','$']
        for move in neighbours:
            if move in self.map.map_dict and move not in self.path_find_visited and self.map.map_dict[move] \
                    in empty_block_symbols:
                available_neighbours.append(move)
        return available_neighbours

    def random_walk_get_neighbours(self, current):
        x, y = current
        neighbours = [(x + 1, y), (x, y + 1), (x - 1, y), (x, y - 1)]
        available_neighbours = []
        empty_block_symbols = [' ', 'd', 'k', 'a', '$']
        if self.have_axe:
            empty_block_symbols += ['T']
        if self.have_key:
            empty_block_symbols += ['-']
        for move in neighbours:
            if move in self.map.map_dict and move not in self.path_find_visited and self.map.map_dict[move] \
                    in empty_block_symbols:
                available_neighbours.append(move)
        return available_neighbours

    def get_cost(self, current, target):
        #Compute Manhattan Distance between current_position and target location.
        return abs(current[0] - target[0]) + abs(current[1] - target[1])

    def path_find(self, target):
        #print(self.random_walk,self.sail_allowed,self.explore_sea,self.on_boat)
        #If agent is on boat, try to go through as less land positions as possible.
        if self.on_boat:
            land_cost = 1000
            sea_cost = 1
        else:
            land_cost=1
            sea_cost=1
        openset = set()
        closedset = set()
        current = self.x, self.y
        # Add the starting point to the open set
        openset.add(current)
        self.cost_dict[current]=(0,0)
        self.heuristic_dict[current]=self.get_cost(current,target)
        # While the open set is not empty
        while openset:
            # Find the item in the open set with the lowest G + H score
            current = sorted(openset, key=lambda node: (self.cost_dict[node][0],self.cost_dict[node][1]+self.heuristic_dict[node]))[0]
            # If it is the item we want, retrace the path and return it
            if current == target and self.have_dynamite>=self.cost_dict[current][0]:
                path = []
                while current in self.parent_dict:
                    path.append(current)
                    current = self.parent_dict[current]
                path.append(current)
                self.cost_dict = {}
                self.heuristic_dict = {}
                self.parent_dict = {}
                return path[::-1]
            # Remove the item from the open set
            openset.remove(current)
            # Add it to the closed set
            closedset.add(current)
            # Loop through the node's children/siblings
            if self.random_walk:
                children = self.random_walk_get_neighbours(current)
            elif self.sail_allowed and self.explore_sea and not self.on_boat:
                children = self.get_neighbours(current)
            elif self.sail_allowed and self.explore_sea and self.on_boat:
                children = self.random_sail_get_neighbours(current)
            else:
                children = self.get_neighbours(current)
            for node in children:
                # If it is already in the closed set, skip it
                if node in closedset:
                    continue
                # Otherwise if it is already in the open set
                if node in openset:
                    # Check if we beat the G score
                    num_dynamites_needed, num_steps = self.cost_dict[current]
                    next_num_dynamites_needed,next_num_steps=self.cost_dict[node]
                    if self.map.map_dict[node] == '*':
                        new_num_dynamites, new_num_steps = num_dynamites_needed+1, num_steps + land_cost
                    elif self.map.map_dict[node] == '~':
                        new_num_dynamites, new_num_steps = num_dynamites_needed, num_steps + sea_cost
                    else:
                        new_num_dynamites, new_num_steps = num_dynamites_needed, num_steps + land_cost
                    if new_num_dynamites<next_num_dynamites_needed:
                        # If so, update the node to have a new parent
                        self.cost_dict[node]=(new_num_dynamites,new_num_steps)
                        self.parent_dict[node]=current
                    elif new_num_dynamites==next_num_dynamites_needed and new_num_steps<next_num_steps:
                        self.cost_dict[node] = (new_num_dynamites, new_num_steps)
                        self.parent_dict[node] = current
                else:
                    num_dynamites_needed, num_steps = self.cost_dict[current]
                    if self.map.map_dict[node] == '*':
                        new_num_dynamites, new_num_steps = num_dynamites_needed+1, num_steps + land_cost
                    elif self.map.map_dict[node] == '~':
                        new_num_dynamites, new_num_steps = num_dynamites_needed, num_steps + sea_cost
                    else:
                        new_num_dynamites, new_num_steps = num_dynamites_needed, num_steps + land_cost
                    # If it isn't in the open set, calculate the G and H score for the node
                    self.cost_dict[node] = (new_num_dynamites, new_num_steps)
                    self.heuristic_dict[node] = self.get_cost(node, target)
                    # Set the parent to our current item
                    self.parent_dict[node] = current
                    # Add it to the set
                    openset.add(node)
        # Throw an exception if there is no path
        self.cost_dict = {}
        self.heuristic_dict ={}
        self.parent_dict = {}
        return

    def path_to_output(self, path):
        #Get next reachable position from path to target position.
        x_n, y_n = path[1]
        x_d = x_n - self.x
        y_d = y_n - self.y
        direction=None
        #Direction juddgement.
        if x_d == -1 and y_d == 0:
            direction = 2
        elif x_d == 1 and y_d == 0:
            direction = 0
        elif x_d == 0 and y_d == 1:
            direction = 3
        elif x_d == 0 and y_d == -1:
            direction = 1
        #If next move could get items. Update item locations
        if self.direction == direction:
            if self.map.map_dict[(x_n, y_n)] == 'k':
                self.have_key = True
                self.key_locations.remove((x_n, y_n))
                self.map.map_dict[(x_n, y_n)] = ' '
            if self.map.map_dict[(x_n, y_n)] == '$':
                self.got_treasure = True
                self.treasure_location = None
                self.map.map_dict[(x_n, y_n)] = ' '
            if self.map.map_dict[(x_n, y_n)] == 'a':
                self.have_axe = True
                self.axe_locations.remove((x_n, y_n))
                self.map.map_dict[(x_n, y_n)] = ' '
            if self.map.map_dict[(x_n, y_n)] == 'd':
                self.have_dynamite += 1
                self.dynamite_locations.remove((x_n,y_n))
                self.map.map_dict[(x_n, y_n)] = ' '
            if self.map.map_dict[(x_n, y_n)] == 'T':
                if self.have_axe:
                    self.map.map_dict[(x_n, y_n)] = ' '
                    self.tree_locations.remove((x_n,y_n))
                    self.have_boat=True
                    return 'c'
                else:
                    self.have_dynamite -= 1
                    self.map.map_dict[(x_n, y_n)] = ' '
                    return 'b'
            elif self.map.map_dict[(x_n, y_n)] == '-':
                self.map.map_dict[(x_n, y_n)] = ' '
                return 'u'
            elif self.map.map_dict[(x_n, y_n)] == '*':
                self.have_dynamite -= 1
                self.map.map_dict[(x_n, y_n)] = ' '
                return 'b'
            else:
                #If agent try to move into land from sea.
                if self.map.map_dict[(x_n, y_n)] != '~' and self.map.map_dict[(self.x, self.y)] == '~':
                    self.have_boat = False
                    self.on_boat = False
                #If agent try to move into sea from land.
                if self.map.map_dict[(x_n, y_n)] == '~' and self.map.map_dict[(self.x, self.y)] != '~':
                    self.have_boat = False
                    self.on_boat = True
                return 'f'
        else:
            d_d = (direction - self.direction) % 4
            if d_d <= 2:
                return 'r'
            else:
                return 'l'

    def get_direction(self, direction, action):
        if action == 'l':
            return (direction - 1) % 4
        else:
            return (direction + 1) % 4


    def update_map(self, window, action):
        #If this is first message received from server, initialize map_dict.
        if len(self.map.map_dict) == 0:
            self.map.map_dict = copy.deepcopy(window)
            for loc in self.map.map_dict:
                if self.map.map_dict[loc] == 'k':
                    self.key_locations.add(loc)
                elif self.map.map_dict[loc] == 'T':
                    self.tree_locations.add(loc)
                elif self.map.map_dict[loc] == 'a':
                    self.axe_locations.add(loc)
                elif self.map.map_dict[loc] == '$':
                    self.treasure_location = loc
                elif self.map.map_dict[loc] == 'd':
                    self.dynamite_locations.add(loc)
                elif self.map.map_dict[loc] == '~':
                    self.sea_locations.add(loc)
            self.map.map_dict[(0, 0)] = 's'
            self.map.South_board = -2
            self.map.North_board = 2
            self.map.East_board = 2
            self.map.West_board = -2
        else:
            #According to movement action to update map_dict
            if action == 'l' or action == 'r':
                self.direction = self.get_direction(self.direction, action)
            elif action == 'f':
                if self.direction == 1:
                    self.y -= 1
                    #If agent try to move into wall, tree and door without relevant item, does not update map_dict.
                    if self.map.map_dict[(self.x, self.y)] == '*' or self.map.map_dict[(self.x, self.y)] == 'T' or self.map.map_dict[(self.x, self.y)] == '-':
                        self.y += 1
                        return
                    #Update map after pick item.
                    if self.map.map_dict[self.x,self.y] == 'd' or self.map.map_dict[self.x,self.y] == 'k' or self.map.map_dict[self.x,self.y] == 'a':
                        self.map.map_dict[self.x,self.y] = ' '
                    if self.y - 2< self.map.South_board:
                        self.map.South_board -= 1
                    #Only update map_dict by using new 5 position.
                    for i in range(-2, 3):
                        loc=(self.x + i,self.y - 2)
                        self.map.map_dict[loc] = window[(i, -2)]
                        #Update item location.
                        if window[(i, -2)]== 'k':
                            self.key_locations.add(loc)
                        elif window[(i, -2)] == 'd':
                            self.dynamite_locations.add(loc)
                        elif window[(i, -2)] == 'a':
                            self.axe_locations.add(loc)
                        elif window[(i, -2)] == 'T':
                            self.tree_locations.add(loc)
                        elif window[(i, -2)] == '~':
                            self.sea_locations.add(loc)
                        elif window[(i, -2)] == '$':
                            self.treasure_location = loc
                        elif window[(i, -2)] == '*':
                            self.wall_locations.add(loc)
                if self.direction == 3:
                    self.y += 1
                    #If agent try to move into wall, tree and door without relevant item, does not update map_dict.
                    if self.map.map_dict[(self.x, self.y)] == '*' or self.map.map_dict[(self.x, self.y)] == 'T' or \
                                    self.map.map_dict[(self.x, self.y)] == '-':
                        self.y -= 1
                        return
                    #Update map after pick item.
                    if self.map.map_dict[self.x,self.y] == 'd' or self.map.map_dict[self.x,self.y] == 'k' or self.map.map_dict[self.x,self.y] == 'a':
                        self.map.map_dict[self.x,self.y] = ' '
                    if self.y + 2 > self.map.North_board:
                        self.map.North_board += 1
                    #Only update map_dict by using new 5 position.
                    for i in range(-2, 3):
                        loc = (self.x - i , self.y + 2)
                        self.map.map_dict[loc] = window[(i, -2)]
                        if window[(i, -2)]== 'k':
                            self.key_locations.add(loc)
                        elif window[(i, -2)] == 'd':
                            self.dynamite_locations.add(loc)
                        elif window[(i, -2)] == 'a':
                            self.axe_locations.add(loc)
                        elif window[(i, -2)] == 'T':
                            self.tree_locations.add(loc)
                        elif window[(i, -2)] == '~':
                            self.sea_locations.add(loc)
                        elif window[(i, -2)] == '$':
                            self.treasure_location = loc
                        elif window[(i, -2)] == '*':
                            self.wall_locations.add(loc)
                if self.direction == 0:
                    self.x += 1
                    #If agent try to move into wall, tree and door without relevant item, does not update map_dict.
                    if self.map.map_dict[(self.x, self.y)] == '*' or self.map.map_dict[(self.x, self.y)] == 'T' or \
                                    self.map.map_dict[(self.x, self.y)] == '-':
                        self.x -= 1
                        return
                    #Update map after pick item.
                    if self.map.map_dict[self.x,self.y] == 'd' or self.map.map_dict[self.x,self.y] == 'k' or self.map.map_dict[self.x,self.y] == 'a':
                       self.map.map_dict[self.x,self.y] = ' '
                    if self.x + 2> self.map.East_board:
                        self.map.East_board += 1
                    #Only update map_dict by using new 5 position.
                    for i in range(-2, 3):
                        loc = (self.x + 2, self.y + i)
                        self.map.map_dict[loc] = window[(i, -2)]
                        if window[(i, -2)]== 'k':
                            self.key_locations.add(loc)
                        elif window[(i, -2)] == 'd':
                            self.dynamite_locations.add(loc)
                        elif window[(i, -2)] == 'a':
                            self.axe_locations.add(loc)
                        elif window[(i, -2)] == 'T':
                            self.tree_locations.add(loc)
                        elif window[(i, -2)] == '~':
                            self.sea_locations.add(loc)
                        elif window[(i, -2)] == '$':
                            self.treasure_location = loc
                        elif window[(i, -2)] == '*':
                            self.wall_locations.add(loc)
                if self.direction == 2:
                    self.x -= 1
                    #If agent try to move into wall, tree and door without relevant item, does not update map_dict.
                    if self.map.map_dict[(self.x, self.y)] == '*' or self.map.map_dict[(self.x, self.y)] == 'T' or \
                                    self.map.map_dict[(self.x, self.y)] == '-':
                        self.x += 1
                        return
                    #Update map after pick item.
                    if self.map.map_dict[self.x,self.y] == 'd' or self.map.map_dict[self.x,self.y] == 'k' or self.map.map_dict[self.x,self.y] == 'a':
                        self.map.map_dict[self.x,self.y] = ' '
                    if self.x - 2 < self.map.West_board:
                        self.map.West_board -= 1
                    #Only update map_dict by using new 5 position.
                    for i in range(-2, 3):
                        loc = (self.x - 2, self.y - i)
                        self.map.map_dict[loc] = window[(i, -2)]
                        if window[(i, -2)]== 'k':
                            self.key_locations.add(loc)
                        elif window[(i, -2)] == 'd':
                            self.dynamite_locations.add(loc)
                        elif window[(i, -2)] == 'a':
                            self.axe_locations.add(loc)
                        elif window[(i, -2)] == 'T':
                            self.tree_locations.add(loc)
                        elif window[(i, -2)] == '~':
                            self.sea_locations.add(loc)
                        elif window[(i, -2)] == '$':
                            self.treasure_location=loc
                        elif window[(i, -2)] == '*':
                            self.wall_locations.add(loc)
            

class Map:
    def __init__(self):
        self.South_board = 0
        self.North_board = 0
        self.East_board = 0
        self.West_board = 0
        self.map_dict = {}

    def print_map(self):
        for y in range(self.North_board, self.South_board - 1, -1):
            for x in range(self.West_board, self.East_board + 1):
                if (x, y) in self.map_dict:
                    print(self.map_dict[(x, y)], end='')
                else:
                    print('!', end='')
            print()

window = {}
action = None
robot = Agent()
while True:
    print(messg)
    for y in range(-2, 3):
        for x in range(2, -3,-1):
            if not (x == 0 and y == 0):
                ch = messg.read(1)
                if not ch:
                    sys.exit()
                window[(x,y)] = ch
    robot.update_map(window, action)
    robot.map.print_map()
    #print(robot.path_find((0,1)))
    # action = input('action:')
        
    action = robot.make_decision()
    Clientsocket.send(action.encode())
