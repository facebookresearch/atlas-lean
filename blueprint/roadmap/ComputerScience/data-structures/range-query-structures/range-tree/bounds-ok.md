# Bounds-valid range trees

For a range tree $s$, write $s_{\min}$ and $s_{\max}$ for its
cached lower and upper bounds: the stored interval endpoints at a node, the value itself at a
leaf, and $0$ for the empty tree. Bounds-validity is defined inductively: the empty tree and every
leaf are bounds-valid, and a node with cached interval $[a, b]$, left child $\ell$ and right child
$r$ is bounds-valid when $\ell$ and $r$ are bounds-valid, each of them has at least one leaf,
$a = \min(\ell_{\min}, r_{\min})$ and $b = \max(\ell_{\max}, r_{\max})$.

The children must be nonempty because the empty tree has cached bounds $0$: with an empty child
the node cache would only enclose the leaves (a node over an empty child and the single leaf $5$
could cache $[0, 5]$), not equal their true interval. In a bounds-valid tree every leaf value lies
in the cached interval, and if the tree has a leaf, both cached bounds are leaf values.
