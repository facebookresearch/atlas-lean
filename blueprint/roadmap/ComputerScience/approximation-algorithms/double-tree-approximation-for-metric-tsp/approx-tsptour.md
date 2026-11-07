# The APPROX-TSP-TOUR algorithm

CLRS `APPROX-TSP-TOUR`, steps 3 and 4: given a root $r$
and a forest $F$ (the subtrees of a spanning tree with root $r$), return the tour that lists $r$
followed by the vertices of $F$ in preorder. As a timed computation it charges one unit for $r$
and one unit for each vertex visited by the preorder walk of $F$.
