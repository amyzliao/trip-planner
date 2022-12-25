#lang dssl2

let eight_principles = ["Know your rights.",
"Acknowledge your sources.",
"Protect your work.",
"Avoid suspicion.",
"Do your own work.",
"Never falsify a record or permit another person to do so.",
"Never fabricate data, citations, or experimental results.",
"Always tell the truth when discussing your work with your instructor."]

# Final project: Trip Planner

import cons
import sbox_hash
import 'project-lib/dictionaries.rkt'
import 'project-lib/graph.rkt'
import 'project-lib/binheap.rkt'

### Basic Types ###

#  - Latitudes and longitudes are numbers:
let Lat?  = num?
let Lon?  = num?

#  - Point-of-interest categories and names are strings:
let Cat?  = str?
let Name? = str?

### Raw Item Types ###

#  - Raw positions are 2-element vectors with a latitude and a longitude
let RawPos? = TupC[Lat?, Lon?]

#  - Raw road segments are 4-element vectors with the latitude and
#    longitude of their first endpoint, then the latitude and longitude
#    of their second endpoint
let RawSeg? = TupC[Lat?, Lon?, Lat?, Lon?]

#  - Raw points-of-interest are 4-element vectors with a latitude, a
#    longitude, a point-of-interest category, and a name
let RawPOI? = TupC[Lat?, Lon?, Cat?, Name?]

### Contract Helpers ###

# ListC[T] is a list of `T`s (linear time):
let ListC = Cons.ListC
# List of unspecified element type (constant time):
let List? = Cons.list?


interface TRIP_PLANNER:

    # Returns the positions of all the points-of-interest that belong to
    # the given category.
    def locate_all(
            self,
            dst_cat:  Cat?           # point-of-interest category
        )   ->        ListC[RawPos?] # positions of the POIs

    # Returns the shortest route, if any, from the given source position
    # to the point-of-interest with the given name.
    def plan_route(
            self,
            src_lat:  Lat?,          # starting latitude
            src_lon:  Lon?,          # starting longitude
            dst_name: Name?          # name of goal
        )   ->        ListC[RawPos?] # path to goal

    # Finds no more than `n` points-of-interest of the given category
    # nearest to the source position.
    def find_nearby(
            self,
            src_lat:  Lat?,          # starting latitude
            src_lon:  Lon?,          # starting longitude
            dst_cat:  Cat?,          # point-of-interest category
            n:        nat?           # maximum number of results
        )   ->        ListC[RawPOI?] # list of nearby POIs

struct position:
    let lat: Lat?
    let long: Lon?

struct poi:
    let location: position?
    let category: Cat?
    let name: Name?

class TripPlanner (TRIP_PLANNER):
    let _size: num? # total number of distinct positions
    let _num_pois: num? # number of pois
    let _graph # WuGraph:adjacencymatrix of positions = nodes, roads = edges, length of roads = weights
    let _position_to_node_id # dict:hashtable that maps positions to node ids of the WuGraph
    let _node_id_to_position # dict:vec that maps node ids (indexes) to positions
    let _position_features # 2Dlist:vec of linked lists where indices are position ids, elements are linked list of pois at that position
    
    def __init__(self, roads: VecC[RawSeg?], pois: VecC[RawPOI?]):
            # roads is a vector of raw road segments
            # pois is a vector of raw pois
        self._num_pois = pois.len()
        # the largest possible number of positions is capped by 2x number of roads, if each road
        # connects two positions, and each position is distinct
        let max_size = roads.len() * 2
        self._position_to_node_id = HashTable(max_size, make_sbox_hash())
        self._node_id_to_position = vec(max_size)
        self._graph = WuGraph(max_size)
        # fill our dicts and graph with positions in the roads vector (no duplicate positions)
        for road in roads:
            let x1 = road[0]
            let y1 = road[1]
            let x2 = road[2]
            let y2 = road[3]
            let length = ((x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2)).sqrt()
            let p1 = position(x1, y1)
            let p2 = position(x2, y2)
            if not self._position_to_node_id.mem?(p1):
                self._position_to_node_id.put(p1, self._position_to_node_id.len())
                self._node_id_to_position[self._position_to_node_id.get(p1)] = p1
            if not self._position_to_node_id.mem?(p2):
                self._position_to_node_id.put(p2, self._position_to_node_id.len())
                self._node_id_to_position[self._position_to_node_id.get(p2)] = p2
            self._graph.set_edge(self._position_to_node_id.get(p1), self._position_to_node_id.get(p2), length)
        # update self._size to the length of the dictionary (number of distinct positions)
        self._size = self._position_to_node_id.len()
        # fill our 2D list of pois at each position
        self._position_features = vec(self._size)
        for p in pois:
            let pos = position(p[0], p[1])
            let newpoi = poi(pos, p[2], p[3])
            let pos_id = self._position_to_node_id.get(pos)
            let prev_head = self._position_features[pos_id]
            self._position_features[pos_id] = cons(newpoi, prev_head)
        
    # Returns the raw positions of all the points-of-interest that belong to
    # the given category. No duplicate positions.
    def locate_all(
            self,
            dst_cat:  Cat?           # point-of-interest category
        )   ->        ListC[RawPos?]: # positions of the POIs
        let r = None
        for i, poi_list in self._position_features:
            let curr = poi_list
            while curr: # is not None
                if curr.data.category == dst_cat:
                    # add the position to r
                    let pos = self._node_id_to_position[i]
                    let rawpos = [pos.lat, pos.long]
                    r = cons(rawpos, r)
                    break
                curr = curr.next
        return r
                

    # Returns the shortest route, if any, from the given source position
    # to the point-of-interest with the given name.
    def plan_route(
            self,
            src_lat:  Lat?,          # starting latitude
            src_lon:  Lon?,          # starting longitude
            dst_name: Name?          # name of goal (name of poi)
        )   ->        ListC[RawPos?]: # path to goal (shortest)
        # return list
        let r = None
        # find node id of start position
        let start_pos = position(src_lat, src_lon)
        let start_node = self._position_to_node_id.get(start_pos)
        # find node id of end position (position of poi with name dst_name)
        let end_node = None
        for i, poi_list in self._position_features:
            let curr = poi_list
            while curr: # is not None
                if curr.data.name == dst_name:
                    end_node = i
                    break
                curr = curr.next
            if end_node: # is not None
                break
        # if no poi with given name, return empty list
        if not end_node:
            return r
        # run dijkstra's algorithm
        let dijk_table = self._dijkstra(start_node)
        # if destination node is unreachable, return empty list
        if dijk_table[0][end_node] == inf:
            return r
        # if it's reachable, return the shortest path in a cons list of positions
        let curr = end_node
        while not curr == start_node:
            let pos = self._node_id_to_position[curr]
            let rawpos = [pos.lat, pos.long]
            r = cons(rawpos, r)
            curr = dijk_table[1][curr]
        r = cons([start_pos.lat, start_pos.long], r)
        return r


    # Finds no more than `n` points-of-interest of the given category
    # nearest to the source position.
    def find_nearby(
            self,
            src_lat:  Lat?,          # starting latitude
            src_lon:  Lon?,          # starting longitude
            dst_cat:  Cat?,          # point-of-interest category
            n:        nat?           # maximum number of results
        )   ->        ListC[RawPOI?]: # list of nearby POIs
        let r = None
        # find node id of start position
        let start_node = self._position_to_node_id.get(position(src_lat, src_lon))
        # run dijkstra's algo to find shortest paths to each position
        let dijk_table = self._dijkstra(start_node)
        # insert pois of correct category into binary heap; order by distance of its position to start
        let poi_heap = BinHeap[poi?](self._num_pois, lambda a, b: \
                                        dijk_table[0][self._position_to_node_id.get(a.location)] < \
                                        dijk_table[0][self._position_to_node_id.get(b.location)])
        for i, poi_list in self._position_features:
            if dijk_table[0][i] is not inf: # only consider pois in reachable positions
                let curr = poi_list
                while curr: # is not None
                    if curr.data.category == dst_cat:
                        poi_heap.insert(curr.data)
                    curr = curr.next
        # while heap is not empty, remove and add to return list the n closest pois to start
        while poi_heap.len() > 0 and n > 0:
            let p = poi_heap.find_min()
            let rawpoi = [p.location.lat, p.location.long, p.category, p.name]
            r = cons(rawpoi, r)
            n = n - 1
            poi_heap.remove_min()
        return r
        
        
    # takes a starting node and runs dijkstra's algorithm.
    # returns an array with element 0 storing the distance map and element 1 
    # storing the predecessors map.
    def _dijkstra(self, start: nat?):
        # initialize tables for distances and predecessors
        let dist = vec(self._size) # maps nodes to distance to that node from start
        let pred = vec(self._size) # maps nodes to predecessor of that node
        for i in range(self._size):
            dist[i] = inf
            pred[i] = None
        dist[start] = 0
        # initialize priority queue. max capacity is |E| < |V|^2
        let todo = BinHeap[nat?](self._size * self._size, lambda x, y: dist[x] < dist[y])
        let done = [False; self._size]
        todo.insert(start)
        # relax edges using Dijkstra's algorithm
        while todo.len() > 0:
            let v = todo.find_min()
            todo.remove_min()
            if not done[v]:
                done[v] = True
                let vlist = self._graph.get_adjacent(v)
                while vlist:
                    let w = self._graph.get_edge(v, vlist.data)
                    if dist[v] + w < dist[vlist.data]:
                        dist[vlist.data] = dist[v] + w
                        pred[vlist.data] = v
                        todo.insert(vlist.data)
                    vlist = vlist.next
        let table = [dist, pred]
        return table
        
def sort_rawpos(rawpos_lst):
    def rawpos_lt?(rp1, rp2):
        return rp1[0] < rp2[0] or (rp1[0] == rp2[0] and rp1[1] < rp2[1])
    Cons.sort[RawPos?](rawpos_lt?, rawpos_lst)

def my_first_example():
    return TripPlanner([[0,0, 0,1], [0,0, 1,0], [0,0, 1,1], [1,1, 2,1]],
                       [[0,0, "bar", "The Empty Bottle"],
                        [0,1, "food", "Pelmeni"],
                        [0,0, "bar", "Bingus"],
                        [1,0, "food", "Popps"],
                        [0,1, "food", "Billy"],
                        [0,1, "bar", "Tilly"],
                        [1,1, "food", "Penguin"],
                        [1,1, "bar", "Benjamins"],
                        [2,1, "food", "Papa"],
                        [2,1, "food", "Cold stone"]])
        
def pdf_example():
    return TripPlanner([[0,0, 1,0],
                        [0,0, 0,1],
                        [1,0, 1,1],
                        [0,1, 1,1],
                        [0,1, 0,2],
                        [1,1, 1,2],
                        [0,2, 1,2],
                        [1,2, 1,3],
                        [1,3, -0.2,3.3]],
                       [[0,0, "food", "Sandwiches"],
                        [0,1, "food", "Pasta"],
                        [0,1, "clothes", "Pants"],
                        [1,1, "bank", "Local Credit Union"],
                        [1,3, "bar", "Bar None"],
                        [1,3, "bar", "H Bar"],
                        [-0.2, 3.3, "food", "Burritos"]])
                        
def disc_example():
    return TripPlanner([[0,0, 2,5],
                        [0,0, 3,2],
                        [1,0, 2,5],
                        [1,0, 3,2],
                        [1,0, 4,0],
                        [2,5, 3,2],
                        [3,2, 4,0],
                        [3,2, 6,0],
                        [5,4, 5,5],
                        [5,4, 6,3],
                        [6,3, 5,5]],
                       [[0,0, "food", "A"],
                        [0,0, "bar", "B"],
                        [1,0, "mall", "C"],
                        [1,0, "bar", "N"],
                        [2,5, "park", "F"],
                        [2,5, "food", "E"],
                        [3,2, "airport", "L"],
                        [4,0, "park", "O"],
                        [6,0, "hospital", "I"],
                        [6,0, "food", "H"],
                        [5,4, "airport", "M"],
                        [5,5, "hospital", "J"],
                        [5,5, "park", "G"],
                        [6,3, "bar", "K"],
                        [6,3, "mall", "D"]])

test 'My first locate_all test':
    assert sort_rawpos(my_first_example().locate_all("food")) == \
        Cons.from_vec([[0,1], [1,0], [1,1], [2,1]])
    assert sort_rawpos(my_first_example().locate_all("bar")) == \
        Cons.from_vec([[0,0], [0,1], [1,1]])
        
        
test 'pdf_example locate_all':
    assert sort_rawpos(pdf_example().locate_all("food")) == \
        Cons.from_vec([[-0.2, 3.3], [0,0], [0,1]])
    assert sort_rawpos(pdf_example().locate_all("bank")) == \
        Cons.from_vec([[1,1]])
    assert sort_rawpos(pdf_example().locate_all("bar")) == \
        Cons.from_vec([[1,3]])
    assert sort_rawpos(pdf_example().locate_all("barber")) == \
        Cons.from_vec([])

test 'disc_example locate_all':
    assert sort_rawpos(disc_example().locate_all("food")) == \
        Cons.from_vec([[0,0], [2,5], [6,0]])
    assert sort_rawpos(disc_example().locate_all("bar")) == \
        Cons.from_vec([[0,0], [1,0], [6,3]])
    assert sort_rawpos(disc_example().locate_all("airport")) == \
        Cons.from_vec([[3,2], [5,4]])

test 'My first plan_route test':
   assert my_first_example().plan_route(0, 0, "Pelmeni") == \
       cons([0,0], cons([0,1], None))
   assert my_first_example().plan_route(0, 0, "Penguin") == \
       cons([0,0], cons([1,1], None))
   assert my_first_example().plan_route(0, 0, "Papa") == \
       cons([0,0], cons([1,1], cons([2,1], None)))
   assert my_first_example().plan_route(0, 1, "Cold stone") == \
       cons([0,1], cons([0,0], cons([1,1], cons([2,1], None))))
   assert my_first_example().plan_route(1, 1, "Benjamins") == \
       cons([1,1], None)
   assert my_first_example().plan_route(1, 1, "Tilly") == \
       cons([1,1], cons([0,0], cons([0,1], None)))
   assert my_first_example().plan_route(1, 1, "Pickles") == \
       Cons.from_vec([])

test 'pdf_example plan_route':
   assert pdf_example().plan_route(0, 0, "Sandwiches") == \
       cons([0,0], None)
   assert pdf_example().plan_route(0, 1, "Sandwiches") == \
       cons([0,1], cons([0,0], None))
   assert ((pdf_example().plan_route(1, 1, "Sandwiches") == \
                cons([1,1], cons([0,1], cons([0,0], None)))) or \
           (pdf_example().plan_route(1, 1, "Sandwiches") == \
                cons([1,1], cons([1,0], cons([0,0], None)))))
   assert pdf_example().plan_route(1, 1, "Burritos") == \
       cons([1,1], cons([1,2], cons([1,3], cons([-0.2,3.3], None))))
   assert pdf_example().plan_route(1, 1, "Sushi") == \
       Cons.from_vec([])

test 'disc_example plan_route':
    assert disc_example().plan_route(0,0, "M") == \
        Cons.from_vec([])
    assert disc_example().plan_route(0,0, "B") == \
        cons([0,0], None)
    assert disc_example().plan_route(1,0, "B") == \
        cons([1,0], cons([3,2], cons([0,0], None)))
    assert disc_example().plan_route(2,5, "A") == \
        cons([2,5], cons([0,0], None))
    assert disc_example().plan_route(5,4, "G") == \
        cons([5,4], cons([5,5], None))
    assert disc_example().plan_route(6,3, "I") == \
        Cons.from_vec([])
    assert disc_example().plan_route(2,5, "O") == \
        Cons.from_vec([[2,5], [3,2], [4,0]])
    assert disc_example().plan_route(4,0, "B") == \
        Cons.from_vec([[4,0], [3,2], [0,0]])
   
def sort_rawpoi(rawpoi_lst):
    def rawpoi_lt?(rp1, rp2):
        return rp1[3] < rp2[3]
    Cons.sort[RawPOI?](rawpoi_lt?, rawpoi_lst)
    
test 'My first find_nearby test':
    assert ((my_first_example().find_nearby(0, 0, "food", 1) == \
                cons([0,1, "food", "Pelmeni"], None)) or \
            (my_first_example().find_nearby(0, 0, "food", 1) == \
                cons([0,1, "food", "Billy"], None)) or \
            (my_first_example().find_nearby(0, 0, "food", 1) == \
                cons([1,0, "food", "Popps"], None)))
    assert my_first_example().find_nearby(2,1, "bar", 1) == \
        cons([1,1, "bar", "Benjamins"], None)
    assert sort_rawpoi(my_first_example().find_nearby(2,1, "bar", 3)) == \
        cons([1,1, "bar", "Benjamins"], \
        cons([0,0, "bar", "Bingus"], \
        cons([0,0, "bar", "The Empty Bottle"], None)))
    assert sort_rawpoi(my_first_example().find_nearby(1,0, "bar", 3)) == \
        cons([0,0, "bar", "Bingus"], \
        cons([0,0, "bar", "The Empty Bottle"], \
        cons([0,1, "bar", "Tilly"], None)))
    assert sort_rawpoi(my_first_example().find_nearby(1,1, "food", 3)) == \
        cons([2,1, "food", "Cold stone"], \
        cons([2,1, "food", "Papa"], \
        cons([1,1, "food", "Penguin"], None)))
    assert my_first_example().find_nearby(1,1, "mall", 2) == \
        Cons.from_vec([])


test 'pdf_example find_nearby':
    assert pdf_example().find_nearby(1,3, "food", 1) == \
        cons([-0.2, 3.3, "food", "Burritos"], None)
    assert pdf_example().find_nearby(0,2, "food", 1) == \
        cons([0, 1, "food", "Pasta"], None)
    assert sort_rawpoi(pdf_example().find_nearby(0,2, "food", 2)) == \
        cons([0,1, "food", "Pasta"], \
        cons([0,0, "food", "Sandwiches"], None))
    assert sort_rawpoi(pdf_example().find_nearby(0,2, "food", 3)) == \
        cons([-0.2, 3.3, "food", "Burritos"], \
        cons([0,1, "food", "Pasta"], \
        cons([0,0, "food", "Sandwiches"], None)))
    assert sort_rawpoi(pdf_example().find_nearby(0,2, "food", 4)) == \
        cons([-0.2, 3.3, "food", "Burritos"], \
        cons([0,1, "food", "Pasta"], \
        cons([0,0, "food", "Sandwiches"], None)))
    assert (sort_rawpoi(pdf_example().find_nearby(0,2, "bar", 1)) == \
                cons([1,3, "bar", "Bar None"], None) or \
            sort_rawpoi(pdf_example().find_nearby(0,2, "bar", 1)) == \
                cons([1,3, "bar", "H Bar"], None))
    assert sort_rawpoi(pdf_example().find_nearby(0,2, "bar", 2)) == \
        cons([1,3, "bar", "Bar None"], \
        cons([1,3, "bar", "H Bar"], None))
    assert sort_rawpoi(pdf_example().find_nearby(0,2, "bar", 3)) == \
        cons([1,3, "bar", "Bar None"], \
        cons([1,3, "bar", "H Bar"], None))
    assert pdf_example().find_nearby(0,2, "school", 5) == \
        Cons.from_vec([])
        
test 'disc_example find_nearby':
    assert disc_example().find_nearby(5,4, "food", 4) == \
        Cons.from_vec([])
    assert disc_example().find_nearby(3,2, "park", 2) == \
        cons([2,5, "park", "F"], \
        cons([4,0, "park", "O"], None))
    assert disc_example().find_nearby(3,2, "park", 1) == \
        cons([4,0, "park", "O"], None)
    