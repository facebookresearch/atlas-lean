# Greedy step of online bipartite matching

Consider a bipartite graph with left vertices
$0, \dots, a-1$ and right vertices $0, \dots, b-1$, and an assignment $m$ giving each right
vertex either a left partner or none. On the arrival of a right vertex $j$, the greedy step
returns the assignment that agrees with $m$ at every right vertex other than $j$, and gives $j$
the smallest left neighbour of $j$ that is free in $m$ (the partner of no right vertex), or no
partner if $j$ has no free neighbour.
