# Accumulated inorder traversal of a 2-3 tree

For a 2-3 tree $t$ and a list $s$, the
accumulated traversal $F(t, s)$ is defined by recursion on $t$: for a leaf, $F(t, s) = s$; for
a 2-node with key $a$ and children $l, r$, $F(t, s)$ is $F(l, s')$ where $s'$ is $a$ prepended
to $F(r, s)$; for a 3-node with keys $a, b$ and children $l, m, r$, $F(t, s)$ is $F(l, s')$
where $s'$ is $a$ prepended to $F(m, s'')$ and $s''$ is $b$ prepended to $F(r, s)$.

The result is the inorder traversal of $t$ followed by $s$. It is built without recopying the
traversals of left subtrees.
