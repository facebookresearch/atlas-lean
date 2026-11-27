# Red-black deletion yields a valid red-black tree

For every linearly ordered key type,
every key $x$ and every red-black tree $t$, the tree obtained by deleting $x$ from $t$ is a valid
red-black tree: it is ordered, no red node has a red child, every root-to-leaf path contains the
same number of black nodes, and its root is black (the empty tree counts as black). No hypothesis
on $t$ is needed.

The result is valid because deletion rebuilds the tree by repeated insertion, which always
produces a valid red-black tree.
