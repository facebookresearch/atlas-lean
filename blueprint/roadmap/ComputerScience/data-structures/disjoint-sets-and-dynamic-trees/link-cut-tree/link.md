# Linking two trees of a link-cut tree state

Given vertices $x$ and $y$ and a state $s$,
the state $\operatorname{link}(x, y, s)$ has no preferred edges (all edges dashed), and its
forest is defined as follows. If $x$ or $y$ is not a vertex of the forest, the forest is
unchanged. Otherwise let $t_x$ and $t_y$ be the first represented trees containing $x$ and $y$.
If $x$ is a vertex of $t_y$, the forest is unchanged. Otherwise $t_x$ is rerooted at $x$ (the
edges on its old root-to-$x$ path are reversed, so $x$ becomes its root), the result is
attached as a new last child subtree of the first node labelled $y$ in $t_y$, which adds the
edge from $y$ to $x$, and this joined tree replaces every tree containing $x$ or $y$, placed at
the end of the forest.
