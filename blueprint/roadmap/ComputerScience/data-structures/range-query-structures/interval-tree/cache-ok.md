# Executable cache check for interval trees

The Boolean cache check returns true on the
empty tree. On a node with stored height $h$, stored size $s$, stored maximum $m$, left subtree
$L$, entry $e$ and right subtree $R$ it returns true exactly when
$h = \max(\operatorname{height} L, \operatorname{height} R) + 1$,
$s = \operatorname{size} L + \operatorname{size} R + 1$, $m$ is the largest of the high endpoint
of $e$ and the cached maxima of those of $L$ and $R$ that are nonempty, and the check returns
true on both $L$ and $R$. Here the height and size of a subtree are its stored fields, and the
empty tree has height and size $0$.

It is used only by the executable invariant checker.
