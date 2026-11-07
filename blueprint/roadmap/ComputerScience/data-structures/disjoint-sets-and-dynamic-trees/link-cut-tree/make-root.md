# Making a vertex the root in a link-cut tree state

Given a vertex $x$ and a state $s$,
the state $\operatorname{makeRoot}(x, s)$ has no preferred edges (all edges dashed), and its
forest is defined as follows. If $x$ is not a vertex of the forest, the forest is unchanged.
Otherwise the first represented tree containing $x$ is rerooted at $x$: the edges on the path
from its old root to $x$ are reversed, and when the tree has distinct vertices every undirected
edge is kept. The rerooted tree replaces every tree containing $x$ and is placed at the end of
the forest.
