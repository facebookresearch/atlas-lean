# Height is one more than the taller child's height

For all natural numbers $n$ and $i$,
in the level-order binary tree with $n$ nodes, if the left child $2i + 1$ of $i$ is a valid index
(that is, $2i + 1 < n$), then the height of $i$ is one more than the larger of the heights of its
children $2i + 1$ and $2i + 2$; otherwise the height of $i$ is $0$. Here an index $j \ge n$ has
height $0$. This is the recursion for the number of edges on a longest downward path from $i$ to
a leaf.
