# Black height of a possibly double-black tree

The black height of a genuine red-black tree
is its usual black height. The double-black empty tree has black height $2$, and a double-black
node with left subtree $L$ has black height $h(L) + 2$, where $h(L)$ is the usual black height of
$L$. Thus a double-black root counts as two black nodes, where the usual black height counts the
empty tree as one.

For an ordered, balanced red-black tree satisfying the red invariant, deleting any key by the
double-black descent, before the root is blackened, yields a tree whose black height in this sense
equals the black height of the original tree.
