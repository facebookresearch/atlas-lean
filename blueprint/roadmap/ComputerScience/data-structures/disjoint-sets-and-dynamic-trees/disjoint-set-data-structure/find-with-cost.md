# Find with cost

For a vertex $x$ of a parent forest $F$, find with cost returns the root
that find returns for $x$, together with the cost $\ell(x) + 1$, where $\ell(x)$ is the path
length of $x$ (the number of non-root parent edges that find traverses from $x$). That is, it
charges one unit for every visited vertex, including the root.
