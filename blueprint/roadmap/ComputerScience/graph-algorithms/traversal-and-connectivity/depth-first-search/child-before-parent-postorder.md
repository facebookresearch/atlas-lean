# A DFS child finishes before its parent

Let $G$ be a directed graph with ordered
adjacency lists and fix an ordered list of roots. If $(c, p)$ is one of the (child, parent) pairs
recorded by the left-first depth-first search of $G$ from these roots, then $c$ occurs before $p$
in the postorder (finish order) of that search.
