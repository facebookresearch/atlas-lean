# Left rotation

Write $\langle L, x, R\rangle$ for a node with left subtree $L$, entry $x$
and right subtree $R$. The left rotation sends $\langle a, x, \langle b, y, c\rangle\rangle$ to
$\langle\langle a, x, b\rangle, y, c\rangle$, where both nodes of the result get freshly
recomputed height, size and maximum high endpoint. Every tree not of this shape is returned
unchanged.
