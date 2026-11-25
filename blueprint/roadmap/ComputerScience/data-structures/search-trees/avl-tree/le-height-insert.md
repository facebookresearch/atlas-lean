# Insertion does not lower the height

Write $h(T)$ for the cached height at the root of a
tree $T$, with $h$ of the empty tree equal to $0$. Let the keys be linearly ordered, and let $T$ be
a tree whose cached heights are correct at every node and which satisfies the AVL balance
invariant at every node. Then for every key $x$, if $T'$ is the tree obtained by inserting $x$
into $T$, we have $h(T) \le h(T')$.
