# Subtree at the end of the search path

Over a linear order, the focus of a key $x$ in a binary tree is defined recursively. The empty
tree has empty focus. For a node with key $k$, left subtree $l$ and right subtree $r$: if $x = k$,
the focus is the node itself; if $x < k$, it is the node itself when $l$ is empty and the focus
of $x$ in $l$ otherwise; if $x > k$, it is the node itself when $r$ is empty and the focus of $x$
in $r$ otherwise.

So the focus is the subtree rooted at the last node visited by the binary-search descent for $x$:
the node holding $x$ if the descent finds it, and otherwise the node at which the descent would
leave the tree through an empty child. This is the node that the [splay operation](splay.md)
brings to the root, and $|\mathrm{focus}(x, t)|$ is the size $s(x)$ in the access lemma.
