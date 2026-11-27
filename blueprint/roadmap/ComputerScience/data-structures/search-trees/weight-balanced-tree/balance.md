# Weight-balanced rebalancing

For binary trees $L$, $R$ and a key $k$, write $|t|$ for
the number of keys of a tree $t$, $w(t) = |t| + 1$ for its weight, $w = w(L) + w(R)$, and
$\langle X, x, Y \rangle$ for the node with key $x$, left subtree $X$ and right subtree
$Y$. The rebalanced node $\mathrm{balance}(L, k, R)$ is defined as follows.
If $3w < 4\,w(L)$, then $L = \langle A, a, B \rangle$ is a node; if $|B| \le 2|A|$, the
result is the single rotation $\langle A, a, \langle B, k, R \rangle \rangle$, and
otherwise $B = \langle B_1, b, B_2 \rangle$ is a node and the result is the double
rotation $\langle \langle A, a, B_1 \rangle, b, \langle B_2, k, R \rangle \rangle$.
Otherwise, if $3w < 4\,w(R)$, then $R = \langle C, c, D \rangle$ is a node; if
$|C| \le 2|D|$, the result is $\langle \langle L, k, C \rangle, c, D \rangle$, and
otherwise $C = \langle C_1, d, C_2 \rangle$ is a node and the result is
$\langle \langle L, k, C_1 \rangle, d, \langle C_2, c, D \rangle \rangle$.
In all remaining cases the result is $\langle L, k, R \rangle$.
