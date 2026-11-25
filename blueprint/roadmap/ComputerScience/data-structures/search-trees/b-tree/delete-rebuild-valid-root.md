# Rebuilding deletion yields a root-valid tree

Let $t \ge 2$. For every key $x$ and every
tree $T$, there is a height $h$ such that the rebuilding deletion of $x$ from $T$ with minimum
degree $t$ is root-valid of minimum degree $t$ and height $h$: all leaves sit at depth $h$, every
node holds at most $2t - 1$ keys, every non-root node holds at least $t - 1$ keys, an internal
root holds at least one key, and an internal node with $k$ keys has $k + 1$ children.

No relation between $h$ and the height of $T$ is claimed.
