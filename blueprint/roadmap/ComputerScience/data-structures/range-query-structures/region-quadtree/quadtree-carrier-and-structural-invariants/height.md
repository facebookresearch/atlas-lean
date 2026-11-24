# Height of a quadtree

The height of a region quadtree is defined recursively: a leaf has height $0$, and a branch
$Q(t_0, t_1, t_2, t_3)$ has height $1 + \max(h(t_0), h(t_1), h(t_2), h(t_3))$, where $h$ denotes
height. It is the maximum number of branches on a path from the root to a leaf.
