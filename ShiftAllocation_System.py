import queue
"""
Author:
    Jun Hirano/33285071
"""


"""
M is the number of company
N is the number of officer
"""
class GraphManagement:
    def __init__(self, preferences :list, officers_per_org :list, min_shifts :int, max_shifts :int) -> None:
        """
        Function description:
            This constructor initializes the graph structure required for assigning shifts to officers based on their preferences,
            minimum and maximum shift constraints, in addition to this by putting mid vertex which is day and shift this graph meet 
            the constraints that officer can not work more than 1 shift per day.
            And the demand from organizations is recorded in each company vertex. It sets up the vertices and edges for the 
            entire scheduling problem and prepares the graph for the Ford-Fulkerson algorithm by removing lower bounds and 
            connecting necessary vertices.

        :Input:
        preferences : list
            A list of lists where each inner list contains the shift preferences (0 or 1) for an officer for all shifts.
        officers_per_org : list
            A list of lists where each inner list contains the demand for officers for each shift for a specific organization.
        min_shifts : int
            The minimum number of shifts an officer is required to work.
        max_shifts : int
            The maximum number of shifts an officer can work.

        :Output, return or postcondition:
        :Time complexity: O(NM)
        :Time complexity analysis: Oo(M + NM + N) = O(MN)
        :Space complexity:
            input space: O(preference + officers_per_org) 
            aux space: O(V) where v is the total number of vertex
        """

        self.preferences, self.officers_per_org, self.min_shifts, self.max_shifts = preferences, officers_per_org, min_shifts, max_shifts
        self.total_d = 30 #Total day
        self.total_s = 3 # Total amount of Shift 
        self.total_v = len(preferences) + self.total_d * len(preferences)  + self.total_d * self.total_s * len(preferences) + self.total_d * self.total_s * len(officers_per_org) + 3
        self.total_demand = 0
        self.vertices = [None] * self.total_v
        self.vertices_partition = None # Indicate the last index that store company combination 
        self.edgeList = [] #Store the edge data e.g[(SO1, SO1D0, 1), (SO1D0, SO1D0S0, 1)]

        self.id_list_shiftDay_v  = []

        self.source_v_id, self.origin_id, self.sink_v_id = 0, 1, self.total_v - 1

        self.vertices[self.source_v_id] = Vertex(self.source_v_id, "Source") #Source edge, this is used in reduced form
        self.vertices[self.sink_v_id] = Vertex(self.sink_v_id, "Sink") #End edge


        #This edge is used as management office. So this edge contain total number of demand as negative
        self.vertices[1] = Vertex(1, "Origin") 

        self.vertices_index_id = 2 # Represents the index value of vertices list and id of vertex as well
        self.generate_shiftday_to_Company(officers_per_org)

        # Now We know the total demand because generateCompanyDayShiftVertices calculate the total demand. Add negative total demand to source vertex
        self.vertices[self.origin_id].demand = -self.total_demand
        self.vertices[self.sink_v_id].demand = self.total_demand

        self.generateOfficerDayShiftVertices(preferences, min_shifts, max_shifts)


        # Optimize the graph to run algorithm. i.e. Remove lower_bound and add edge between all vertex which has demand and source or sink vertex
        # In this method, treat the source to all officer edge loerbound and demand.
        self.removeLowerBoundAndConnectWithSource()
            

    def generate_shiftday_to_Company(self, officers_per_org :list):
        """
        Function description:
            Function to generate each company node and combinations of day and shift node.
        :Input:
            officers_per_org (list): List of lists where each inner list represents the demand of officers per shift for a specific company.
        
        :Output, return or postcondition:
            None. This function updates the internal state of the class by adding vertices and edges to represent companies and their 
            respective shifts.
        
        :Output, return or postcondition:
        :Time complexity:
        :Time complexity analysis:
        :Space complexity:
        :Space complexity analysis:
        """
        for comp in range(len(officers_per_org)):
            total_demand_of_comp = 0
            self.vertices[self.vertices_index_id] = Vertex(self.vertices_index_id, "C" + str(comp))
            for demand in officers_per_org[comp]:
                self.total_demand += demand
                total_demand_of_comp += demand
            total_demand_of_comp = self.total_d * total_demand_of_comp
            self.vertices[self.vertices_index_id].set_demand(total_demand_of_comp)
            self.vertices[self.vertices_index_id].addEdge(self.sink_v_id, total_demand_of_comp) # add two since first two id is 
            self.vertices[self.vertices_index_id].set_property(company = comp)
            self.vertices_index_id += 1
        self.total_demand = self.total_d * self.total_demand
        self.vertices_partition = self.vertices_index_id

        for day_no in range(self.total_d):
            for shft_no in range(self.total_s):
                # for shift_demand in officers_per_org:
                #     cap_to_company += shift_demand[shft_no]
                self.vertices[self.vertices_index_id] = Vertex(self.vertices_index_id, "d" + str(day_no) + "-s" + str(shft_no))
                self.vertices[self.vertices_index_id].set_property(day = day_no, shift = shft_no)
                self.vertices[self.vertices_index_id].isDayShift = True
                self.id_list_shiftDay_v.append(self.vertices_index_id)

                #Connect to company
                for company_v_id in range(len(officers_per_org)):
                    company_v_id_for_addEdge = company_v_id + 2
                    cap = officers_per_org[company_v_id][shft_no]
                    self.vertices[self.vertices_index_id].addEdge(company_v_id_for_addEdge, cap) # add two since first two id is use for source and sink

                self.vertices_index_id += 1
    

    def generateOfficerDayShiftVertices(self, preferences, min_shifts, max_shifts):
        """
        Function description:
            This function creates vertices for each officer and each officer connected with all days vertex. This day vertex also connected 
            with unique shift vertex. 
            It generates vertices for officers, days, and shifts, and connects them with edges to represent the possible assignments 
            and constraints (minimum and maximum day they can waork). The function also establishes connections between the officer shifts and 
            company shifts based on the given preferences.

        :Input:
        preferences : list
            A list of lists where each inner list contains the shift preferences (0 or 1) for an officer for all shifts.
        min_shifts : int
            The minimum number of shifts an officer is required to work.
        max_shifts : int
            The maximum number of shifts an officer can work.

        :Output, return or postcondition:
        :Time complexity: O(NM)
        :Time complexity analysis: Since day and shift loop is constant time, O(N * 30 * 3 * M) =O(NM)
        :Space complexity: O(N) 
        :Space complexity analysis: where N is the size of preference
        """
        #Create the vertex for all combination of SO, D, and S
        for i in range(len(preferences)):
            so_name = "SO" + str(i)
            self.vertices[self.vertices_index_id] = Vertex(self.vertices_index_id, so_name)
            self.vertices[self.vertices_index_id].set_property(securityOfficer = i)
            parent_os_vertex = self.vertices[self.vertices_index_id] # This vertex is going to be used in child loop as parent vertex
            
            self.vertices[self.origin_id].addEdge(self.vertices_index_id, max_shifts, min_shifts) #Add edge source to all officer with lower bound and capacity
            self.edgeList.append(('Origin', so_name, (min_shifts, max_shifts)))

            self.vertices_index_id += 1

            for j in range(self.total_d):
                os_day_name = so_name + "-D" + str(j)
                self.vertices[self.vertices_index_id] = Vertex(self.vertices_index_id, os_day_name)
                self.vertices[self.vertices_index_id].set_property(day = j)
                parent_osDay_vertex = self.vertices[self.vertices_index_id] 

                #Add edge OS to each Day. j is the id of day vertex. 
                #Let parent_os_vertex OS1, add edge to all day vertex O1-D1, O1-D2...
                parent_os_vertex.addEdge(self.vertices_index_id, 1) 
                
                self.vertices_index_id += 1

                self.edgeList.append((so_name, os_day_name, 1))

                shift_id = 0 # 0 ~ 2, three diffrent shift in a day
                for k in preferences[i]:
                    if k == 1: #when its 1 Officer wants to work at that shift. So create vertex
                        os_day_s_name = os_day_name + "-S" + str(shift_id)
                        self.vertices[self.vertices_index_id] = Vertex(self.vertices_index_id, os_day_s_name)
                        self.vertices[self.vertices_index_id].officer_id = i # Specify which officer's vertex it is
                        self.vertices[self.vertices_index_id].set_property(shift = shift_id)


                        osDayShift_vertex = self.vertices[self.vertices_index_id]
                        #Add edge OS-Day to each shift.
                        #Let parent_osDay_vertex OS1-D1, add edge to all shift vertex OS1-D1-S1, OS1-D1-S2, ...
                        parent_osDay_vertex.addEdge(self.vertices_index_id, 1)

                        self.edgeList.append((os_day_name, os_day_s_name, 1))
                        self.vertices_index_id += 1

                        # Add edge from each shift to specific company edge 
                        for dest_id in self.id_list_shiftDay_v:
                            dest_v = self.vertices[dest_id]
                            if dest_v.shift == shift_id and dest_v.day == j: # if the edge has same day and same shift
                                osDayShift_vertex.addEdge(dest_id, 1)
                                self.edgeList.append((os_day_s_name, dest_v.name, 1)) 

                    shift_id += 1

    def removeLowerBoundAndConnectWithSource(self):
        """
        Function description:
            This function modifies the graph to prepare it for the Ford-Fulkerson algorithm by removing lower bound constraints 
            between the origin and security officer vertices. It adjusts the demands of the vertices and updates the edge capacities.
            If no lower bound is present, it directly connects the source vertex to the origin vertex. If a lower bound is present,
            it adjusts the demands and capacities and connects the source to the security officer vertices.

        :Time complexity: O(N)
        :Time complexity analysis: When graph has lower bound, it have to loop O(N) time since origin connected with all officer. 
        :Space complexity: O(1)
        :Space complexity analysis: No input, no aux space
        """
        origin_v = self.vertices[self.origin_id]
        source_v = self.vertices[self.source_v_id]
        lower_bound = self.min_shifts #Since lower_bound between Origin and each SO is same we can use same lower bound

        # if there is no lower bound, connect source to origin
        if lower_bound == 0:
            source_v.addEdge(origin_v.id, -origin_v.demand)
            self.edgeList.append(('Source', 'Origin', -origin_v.demand)) 
        
        else: # if there is lower bound
            for edge in origin_v.edge_list:
                so = self.vertices[edge.v] # In here edge.v is the id of security officer

                so.demand -= self.min_shifts # - incoming 
                origin_v.demand += self.min_shifts # + outcoming

                #Update the Capacity of edge between origin to each SO by substract capacity by lower bound
                edge.cap = edge.cap - edge.low_b

                source_v.addEdge(so.id, -so.demand) # add edge source to each security officer. Since demand is negative when edge had lower bpund, capacity is negative of so demand
                self.edgeList.append(('Source', so.name, -so.demand)) 
            if origin_v.demand < 0: # if the demand is still less than zero after lower bound removal, add edge from source to origin with demand as capacity 
                source_v.addEdge(origin_v.id, -origin_v.demand)
                self.edgeList.append(('Source', 'Origin', -origin_v.demand)) 

    def get_edge(self, u_id :int, dest_id :int): # Find the edge between two adjacency edge
        """
        Function description:
        This function searches for an edge connecting two vertices identified by their IDs in the graph's adjacency list.
        If the edge exists, it returns the edge object; otherwise, it returns None.
        
        :Input:
        u_id : int
            The ID of the source vertex from which the search for the edge will begin.
        dest_id : int
            The ID of the destination vertex to which the edge should connect.

        :Output, return or postcondition:
        edge : Edge or None
        The function returns the edge object if an edge exists between the specified vertices. If no such edge is found, it returns None.

        :Time complexity: O(N)
        :Time complexity analysis: In this data structure in the worst case, vertex can have N(number of officer) edges.
        :Space complexity: O(1)
        Worst time comp
        """
        edge = None
        u = self.vertices[u_id]
        
        for curr_edge in u.edge_list:
            v_id = curr_edge.v
            if v_id == dest_id:
                edge = curr_edge
        return edge


    def __str__(self) -> str:
        return_str = ""
        for vertex in self.vertices:
            return_str = return_str + "," + str(vertex) + "\n"
        return return_str 
    
    def showAllEdges(self):

        result_string = ""
        for vertex in self.vertices:
            if vertex != None:
                result_string = result_string + vertex.name + "(" + str(vertex.id) + ") -> " 
                for edge in vertex.edge_list:
                    v = self.vertices[edge.v]
                    result_string += v.name+"(" + "id: "+ str(v.id) + ", (flow/cap (" + str(edge.flow) +"/"  + str(edge.cap) +")))" + ", "
                result_string += "\n"
        return result_string



    

        


class Vertex:
    def __init__(self, id, name) -> None:
        """
        Function description:
            Initializes a vertex with given ID and name, and sets up its attributes.
            This constructor initializes a vertex in a graph with the provided ID and name. It sets up various attributes 
            that will be used for managing adjacency lists, demands, and other properties relevant to the graph's operations.
            Some attributes are used specifically for certain types of vertices, such as company-day-shift vertices, 
            officer-day vertices, or shift vertices. Additionally, attributes are included to facilitate algorithms like BFS.


        :Input:
        id : int
            The unique identifier for the vertex.
        name : str
            The name of the vertex.
        :Time complexity: O(1)
        :Space complexity: O(1)
        """

        self.edge_list = [] #adjacency_list
        self.id = id
        self.name = name
        self.demand = 0

        self.day = None 
        self.shift = None   
        self.SecurityOfficer = None 
        self.company = None 

        # === Used for bfs ===
        self.discover = False
        self.visited = False
        self.prev_vertex = None

        self.distance = 0

        self.path = []

        self.isSink = False

        # === Used if this vertex is the company-day-shif. store which Officer work this vertex
        self.resultHolder = False
        self.officer_list = [] 

        # === used when this vertex is shift vertex, indicate whose day vertex or shift vertex it is
        self.officer_id = [] # Store SO(security officer) vertex id

        #=====Used for day-shift intemid node
        self.isDayShift = False

        


    def __str__(self) -> str:
        return_string = "(" +str(self.id) + ")" + self.name
        return return_string
    
    def addEdge(self, destination: int, cap: int, low_b: int = 0):
        """
        Function description:
        This method adds an edge from the current vertex to a specified destination vertex with a given capacity. 
        If a lower bound is specified, it includes the lower bound in the edge properties.

        :Input:
        destination : int
            The ID of the destination vertex to which the edge is directed.
        cap : int
            The capacity of the edge.
        low_b : int, optional
            The lower bound of the edge capacity, default is 0.

        :Time complexity: O(1)
        :Space complexity: O(1)
        """
        if low_b != 0:
            new_edge = Edge(self.id, destination, cap, low_b)
        else:
            new_edge = Edge(self.id, destination, cap)

        self.edge_list.append(new_edge)
    
    def addBackWardEdge(self, destination: int, cap: int):
        """
        Adds a backward edge to the vertex's adjacency list. This is used only residual network graph.
 
        Function description:
        This method adds a backward edge from the current vertex to a specified destination vertex with a given capacity. 
        The backward property of the edge is set to indicate its direction is opposite to the flow.

        :Input:
        destination : int
            The ID of the destination vertex to which the backward edge is directed.
        cap : int
            The capacity of the backward edge.

        :Time complexity: O(1)
        :Space complexity: O(1)
        """
        new_edge = Edge(self.id, destination, cap)
        new_edge.set_backward()
        self.edge_list.append(new_edge)
        
    def set_demand(self, demand):
        """
        Sets the demand for the vertex.

        Function description:
        This method sets the demand value for the vertex.

        :Input:
        demand : int
            The demand value to be set for the vertex.

        :Time complexity: O(1)
        :Space complexity: O(1)
        """
        self.demand = demand

    def set_property(self, day=None, shift=None, securityOfficer=None, company=None):
        """
        Sets properties for the vertex.

        Function description:
        This method sets various properties of the vertex, such as day, shift, security officer, and company.
        This function is used when generate the company vertex.

        :Input:
        day : int, optional
            The day associated with the vertex, default is None.
        shift : int, optional
            The shift associated with the vertex, default is None.
        securityOfficer : int, optional
            The security officer associated with the vertex, default is None.
        company : int, optional
            The company associated with the vertex, default is None.

        :Time complexity: O(1)
        :Space complexity: O(1)
        """
        self.day = day
        self.shift = shift  
        self.SecurityOfficer = securityOfficer 
        self.company = company

class Edge():
    def __init__(self, u :int, v :int, cap :int , low_b: int = 0) -> None:
        """
        Initializes an edge with given start and end vertices, capacity, and optional lower bound.

        Function description:
        This constructor initializes an edge in a graph from vertex `u` to vertex `v` with a specified capacity.
        Optionally, a lower bound for the edge capacity can be set. It also initializes the flow to zero and sets
        the `isBackward` flag to False.

        :Input:
        u : int
            The ID of the start vertex of the edge.
        v : int
            The ID of the destination vertex of the edge.
        cap : int
            The capacity of the edge.
        low_b : int, optional
            The lower bound of the edge capacity, default is 0.

        :Time complexity: O(1)
        :Space complexity: O(1)
        """
        # u -> v so u is the start and v is the destination
        self.u = u
        self.v = v
        self.flow = 0
        self.cap = cap
        self.low_b = low_b
        self.isBackward = False
    
    def set_backward(self):
        """
        Sets the edge as a backward edge.

        Function description:
        This method sets the `isBackward` attribute of the edge to True, indicating that the edge
        is a backward edge in the residual graph.

        :Time complexity: O(1)
        :Space complexity: O(1)
        """
        self.isBackward = True





class Ford_fulkerson:
    """
    V is the number of vertex
    E is the number of edge

    Since the structure of graph is always same we can represents V and E with N and M,
    V = N + 30N + 90N + M 
    E = N + 30N + 90N + 90N + 90M + M
    """
    def __init__(self, originalGraph) -> None:
        """
        Initializes the Ford-Fulkerson algorithm with the given original graph.

        Function description:
        This constructor initializes the Ford-Fulkerson algorithm by creating a residual network based on the provided original graph.
        It also initializes the total flow to zero.

        :Input:
        originalGraph : Graph
            The original graph representing the flow network.

        :Time complexity: O(NM)
        :Time complexity analysis: Generate graph takes O(NM) time
        :Space complexity: O(V + E)
        :Space complexity: size of the original graph
        """
        self.originalGraph = originalGraph
        self.resid_network = ResidualNetwork(originalGraph)
        self.flow = 0
        #self.resid_network.show

    def executeFordFulkerson(self):
        """
        Executes the Ford-Fulkerson algorithm to find the maximum flow in the flow network.

        Function description:
        This method repeatedly finds augmenting paths in the residual network and updates the flow until no more 
        augmenting paths are found. It calculates the maximum flow from the source to the sink in the flow network.


        :Output, return or postcondition:
        int
            Returns the maximum flow from the source to the sink in the flow network.

        :Time complexity:
        O(VE^2)

        :Time complexity analysis:
        The outer while loop runs O(F) times, where F is the maximum flow. Each iteration involves finding an augmenting path, 
        which takes O(V + E) time, and updating the residual network, which also takes O(V) time. Therefore, the overall 
        time complexity is O(F * (V + E)).
        Since we learnd in lecture that O(F * (V + E)) = O(VE^2) because F = VE

        :Space complexity:
        O(V + E)

        :Space complexity analysis:
        The space complexity is determined by the space needed to store the residual network, which is O(V + E).
        """
        self.flow = 0
        while self.resid_network.hasAugmentingPath():
            path = self.resid_network.getAugmentingPath()
            self.flow += self.resid_network.min_cap_inPath
            self.resid_network.updateResidualNetwork(path)
        return self.flow
    
    # min cut
    def isFeasible(self):
        """
        Function description:
        This method verifies if the current flow in the network is feasible by checking if the flow on all edges 
        from the source matches their capacities and if the flow on all edges towards the sink matches their capacities.
        It calculates the total flow from the source and the total flow to the sink to determine feasibility.

        :Output, return or postcondition:
        bool
            Returns True if the flow is feasible, meaning all edges from the source have flow equal to their capacities 
            and all edges towards the sink have flow equal to their capacities. Returns False otherwise.

        :Time complexity: O(N + M)
        :Time complexity analysis:
        The method iterates over all edges from the source and all edges towards the sink, which in total is O(N + M).

        :Space complexity: O(1)
        :Space complexity analysis: The method uses a constant amount of additional space for variables.
        """
        source_id = self.originalGraph.source_v_id
        total_flow_fromSource = 0
        total_flow_toSink = 0

        is_feasible = True

        # Check all ednge from source
        for edge in self.originalGraph.vertices[source_id].edge_list:
            if edge.cap != edge.flow:
                is_feasible = False
            total_flow_fromSource += edge.flow
        
        partision = self.originalGraph.vertices_partition

        # Check all edge towards the sink
        for vertex in self.originalGraph.vertices[2:partision]:
            flow = vertex.edge_list[0].flow
            cap = vertex.edge_list[0].cap
            if flow != cap:
                is_feasible = False
            total_flow_toSink += flow

        return is_feasible
    
    def generateResultList(self):
        """
        Function description:
        This method creates a nested list that indicates which officers are assigned to which shifts at which companies 
        on which days. The structure of the list is [officer][company][day][shift], and a value of 1 means the officer 
        is assigned to that shift at that company on that day, while 0 means they are not.

        :Output, return or postcondition:
        list
            Returns a nested list of dimensions [num_Officers][num_Companies][30][3] representing the assignment of officers 
            to shifts at companies. Each element is either 0 or 1.

        :Time complexity: O(V)
        :Time complexity analysis:
        The method iterates over all vertices representing company-day-shift combinations, resulting in a time complexity of O(V).

        :Space complexity: O(N * M * 30 * 3)
        :Space complexity analysis: The method creates a nested list with dimensions corresponding to the number of officers, companies, days, and shifts.
        """
        num_Officers = len(self.originalGraph.preferences)
        num_Companies = len(self.originalGraph.officers_per_org)
        nested_list = [[[[0 for _ in range(3)] for _ in range(30)] 
                for _ in range(num_Companies)] 
               for _ in range(num_Officers)]
        for vertex in self.originalGraph.vertices[2:self.originalGraph.vertices_partition]: # Traverse all company vertex
            for data in vertex.officer_id:
                nested_list[data[0]][vertex.company][data[1]][data[2]] = 1
        return nested_list

class ResidualNetwork:
    def __init__(self, originalGraph) -> None:
        """
        Initializes the residual network based on the original graph.

        Function description:
        This constructor initializes the residual network by creating a graph management instance 
        using the preferences, officers per organization, minimum shifts, and maximum shifts from 
        the original graph. It also sets up initial attributes for managing the minimum capacity 
        in the path and the path found by BFS.

        :Input:
        originalGraph : Graph
            The original graph representing the flow network.

        :Time complexity:
            O(NM): sine generate graph takes O(NM)
        
        """
        self.originalGraph = originalGraph

        self.min_cap_inPath = float('inf')


        self.resid_network = GraphManagement(originalGraph.preferences, originalGraph.officers_per_org, originalGraph.min_shifts, originalGraph.max_shifts)

        self.path_foundByBFS = None  
    
    def hasAugmentingPath(self):
        """
        Function description:
            Check if the path is exist in residual network.
        :Output, return or postcondition:
            bool
                return true if its exists, otherwise return false.
        :Time complexity:
            O(V + E)
        """
        self.path_foundByBFS = self.traverse_bfs()
        if self.path_foundByBFS == None:
            return False
        else:
            return True

    def getAugmentingPath(self):
        """
        Return augmenting path after the execution of hasAugmentingPath()
        """
        return self.path_foundByBFS
    
    def updateResidualNetwork(self, path):
        """
        Function description:
            Updates the residual network and the original network's flow based on the given path.
            This method updates the capacities of the edges in the residual network and adjusts the flow in the original network 
            based on the provided path. It also adds reverse edges to the residual network if they do not already exist. Additionally, 
            it stores which officer is assigned to work at a specific company-day-shift combination.

        :Input:
        path : list
            A list of vertex IDs representing the path found from the source to the sink.

        :Output, return or postcondition:
            The method updates the residual network by adjusting the capacities of the edges along the given path and 
            updates the flow in the original network.

        :Time complexity: O(V * N) = O(V)
        :Time complexity analysis: Loop number of vertex and call get_edge(start, dest) which has O(N) time complexity.
        :Space complexity: O(V)
        :Space complexity analysis: where V is the length of the Path
        """
        so_no = 0
        day_no = 0
        shift_no = 0
        for v in range(len(path) - 1):
            start = path[v] # edge start point
            dest = path[v+1] # edge destination point


            start_v = self.originalGraph.vertices[start]
            dest_v = self.originalGraph.vertices[dest]

            #Store who is going to work in that company specific day and shift
            # and dest_v.resultHolder == True and start_v.officer_id != None
            if start_v.day != None and start_v.isDayShift == False:
                day_no = start_v.day
            elif start_v.SecurityOfficer != None and start_v.isDayShift == False:
                so_no = start_v.SecurityOfficer 
            elif start_v.shift != None and start_v.isDayShift == False:
                shift_no = start_v.shift

            if dest_v.company != None:
                dest_v.officer_id.append((so_no,day_no,shift_no))
                

            curr_edge_resid = self.resid_network.get_edge(start, dest)         

            if curr_edge_resid.isBackward == False and self.resid_network.get_edge(dest, start) == None: # get_edge(edge.v, edge.u) checks if we alrady have reverse edge
                # now we know curr_edge_resid is forward edge and doesn't have reversible edge
                self.add_reversible(curr_edge_resid)

            if self.resid_network.get_edge(start, dest).isBackward == False: #If the path throught the residual forward edge
                resid_forward_edge = self.resid_network.get_edge(start, dest)
                resid_backward_edge = self.resid_network.get_edge(dest, start)

                curr_edge_ori = self.originalGraph.get_edge(start, dest)
            else: # When the path go throught the backwards edge we can get forward edge by swap the start node and destination node
                resid_forward_edge = self.resid_network.get_edge(dest, start)
                resid_backward_edge = self.resid_network.get_edge(start, dest)

                curr_edge_ori = self.originalGraph.get_edge(dest, start)
                
            curr_edge_ori.flow += self.min_cap_inPath # update original graph flow

            # update residual network capacity
            resid_forward_edge.cap = curr_edge_ori.cap - curr_edge_ori.flow
            resid_backward_edge.cap = curr_edge_ori.flow


    def add_reversible(self, forward_edge):
        # Check if we can add reverse edge
        # We can add reverse edge when edge itself is not backward and we can not find reverse edge from graph

        # Add edge start_id -> end_id
        start_id = forward_edge.v
        end_id = forward_edge.u

        start_vertex = self.resid_network.vertices[start_id]
        start_vertex.addBackWardEdge(end_id, 0)
            
            

        
    def traverse_bfs(self) -> list:
        """
        Function description:
        This method performs a BFS traversal to find a path from the source vertex to the sink vertex in the residual network. 
        It discovers and visits vertices while keeping track of the path. When the edge is already discovered or capacity is 0 
        BFS skips that edge. If a path to the sink is found, it backtracks to construct the path and resets the visited vertices
        for future searches.

        :Output, return or postcondition:
            Returns a list of vertex IDs representing the path from the source to the sink if such a path exists.
            If no path is found, it returns None.

        :Time complexity:
        O(V + E)
        :Time complexity analysis:
        The BFS traversal explores all vertices and edges in the graph, leading to a time complexity of O(V + E).
        This BFS is used only for specific data structure therefor O(V + E)

        :Space complexity:
            O(V)
        :Space complexity analysis:
        The queue used for BFS and the list of visited vertex IDs both scale with the number of vertices, leading to a space complexity of O(V).
        """
        discovered = queue.Queue(len(self.resid_network.vertices))
        discovered.put(self.resid_network.source_v_id)
        while discovered.empty() == False:
            id = discovered.get() # get vertex id
            u = self.resid_network.vertices[id] #Get vertex instance by accsessing the vertices array?
            u.visited = True # modify the boolean in vertex instance
            if u.id == self.resid_network.sink_v_id: # if the new visited vertex is sink node
                path = self.back_track()
                self.reset_vertex()
                return path

            for edge in u.edge_list:
                v = self.resid_network.vertices[edge.v] # Get next vertices that current connet with 
                if v.discover == False  and edge.cap > 0:
                    discovered.put(v.id) 
                    v.discover = True
                    v.distance = u.distance + 1
                    if v.prev_vertex == None or v.prev_vertex.distance > u.distance: # if old prev_vertex is more far to source
                        v.prev_vertex = u # Change to the new vertex close to the source
                    
        self.reset_vertex()
        return None
    
    def back_track(self):
        """

        Function description:
        Constructs the path from the sink to the source by backtracking through the vertices.
        This method backtracks from the sink vertex to the source vertex using the `prev_vertex` attribute of each vertex 
        to construct the path. It also keeps track of the minimum capacity along the path.

        :Input:
            None

        :Output, return or postcondition:
        list: Returns a list of vertex IDs representing the path from the source to the sink.

        :Time complexity: O(V) where V is the number of vertex
        :Time complexity analysis: In the worst case length of path is same as total number of vertex
        :Space complexity: O(V)
        :Space complexity analysis: The list 'path' store the vertex.
        """
        current_id = self.resid_network.sink_v_id
        path = []
        self.min_cap_inPath = float('inf')
        while True:
            current_vertex = self.resid_network.vertices[current_id]
            path.insert(0,current_id)
            if current_id == self.resid_network.source_v_id:
                break
            prev_id = current_vertex.prev_vertex.id # back track the id
            
            # in this back_track() we keep track the minimum capacity of the edge through out the path
            edge = self.resid_network.get_edge(prev_id, current_id) # Since this is back tracking, prev_id is the start of the edge
            if edge.cap < self.min_cap_inPath:
                self.min_cap_inPath = edge.cap
            
            current_id = prev_id
        return path

    def reset_vertex(self):
        """
        Function description:
        This method resets the `discover`, `visited`, `prev_vertex`, and `distance` attributes of all vertices in the 
        residual network that are not None. This is typically used after a BFS traversal to prepare the vertices 
        for the next search.

        :Input:
        visited_lst : list
            A list of vertex IDs that were visited during the BFS traversal.

        :Output, return or postcondition:
        None
            The method updates the state of the vertices in the residual network, resetting the attributes `discover`, 
            `visited`, `prev_vertex`, and `distance` to their default values.
        
        :Time complexity: O(V) where V is the number of vertex
        :Time complexity analysis: In the worst case length of path is same as total number of vertex
        :Space complexity: O(1)
        """
        for vertex in self.resid_network.vertices:
                if vertex is not None: # Vertex is None when vertices list is not full and ther are empty space
                    vertex.discover = False
                    vertex.visited = False
                    vertex.prev_vertex = None
                    vertex.distance = 0

"""
V is the number of vertex
E is the number of edge
M is the number of company
N is the number of officer

Since the structure of graph is always same we can represents V and E with N and M,
V = N + 30N + 90N + M = M + N
E = N + 30N + 90N + 90N + 90M + M = N + M
"""
def allocate(preferences :list, officers_per_org :list, min_shifts :int, max_shifts :int):
    """
    Function description:
        Function to allocate shifts to officers based on their preferences and the organization's requirements using the Ford-Fulkerson algorithm.
    
    Approach description (if main function):
        Data structure:
        To run the Ford-Fulkerson algorithm, the graph class generates a graph with demand and lower bounds.
        - The origin node is connected to each security officer.
        - Each security officer is connected to all day nodes, with day nodes connected to shift nodes.
        - This structure ensures that each officer can work only one shift per day.
        - Each shift node is connected to nodes representing all combinations of shifts and days.
        - These combination nodes have edges to all company nodes.
        Example of graph
            origin - OS1 - d1 - s1 ----> S0D1 ----> C1 and C2
                              - s2-----> S2D1 ----> C1 and C2
                              - s3
                   - OS2 - d1 - s1 ----> same as above vertex
                              - s2
                              - s3

    
    :Input:
        preferences (list): List of preferences of officers for shifts.
        officers_per_org (list): List of lists where each inner list represents the demand of officers per shift for a specific organization.
        min_shifts (int): Minimum number of shifts an officer can be allocated.
        max_shifts (int): Maximum number of shifts an officer can be allocated.
    
    :Output, return or postcondition:
        If allocation is feasible, returns a nested list representing the allocation result. If not feasible, returns None.
    
    :Time complexity: O(VE^2)
    :Time complexity analysis: O(VE^2) = (N+M)^3 since V and M is M + N
    :Space complexity: O(V + E)
    :Space complexity analysis: O(V + E) is the size of the network flow
    """
    management_data = GraphManagement(preferences, officers_per_org, min_shifts, max_shifts) # Initialize the graph dat astructre

    algo = Ford_fulkerson(management_data) # Give the graph to algorithm
    
    algo.executeFordFulkerson() # Run algorithm O(VE^2)


    result = algo.isFeasible() #Time complexity: O(N + M)

    if result == False:
        return None
    else:
        result_nestedList = algo.generateResultList() #Time complexity: O(V)
        return result_nestedList

