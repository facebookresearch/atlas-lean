# Left-right double rotation

Write $\langle L, x, R\rangle$ for a node with left subtree
$L$, entry $x$ and right subtree $R$. The left-right rotation sends
$\langle\langle a, x, \langle b, y, c\rangle\rangle, z, d\rangle$ to
$\langle\langle a, x, b\rangle, y, \langle c, z, d\rangle\rangle$, where all three nodes of the
result get freshly recomputed height, size and maximum high endpoint. Every tree not of this
shape is returned unchanged.
