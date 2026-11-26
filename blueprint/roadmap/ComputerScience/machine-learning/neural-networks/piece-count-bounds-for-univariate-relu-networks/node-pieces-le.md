# Piece-count bound for a node of a ReLU network

Let a network with layer widths $d_0, d_1, \dots$ have input width $d_0 = 1$, and let it be a ReLU network through layer $i$, with $d_k > 0$ for every $k < i$. Then, as a function of the real input $x$, the output of each node $j$ of layer $i$ has at most $2^i \prod_{k=1}^{i-1} d_k$ affine pieces. Only the traversed layers are constrained, so widths after layer $i$ may be zero (as in finite-network encodings); positivity of the traversed widths is still needed, since a zero traversed width collapses the product bound.
