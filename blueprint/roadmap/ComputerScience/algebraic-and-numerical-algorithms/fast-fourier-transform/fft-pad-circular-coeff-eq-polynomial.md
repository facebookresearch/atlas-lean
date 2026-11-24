# Zero padding turns cyclic convolution into the polynomial product

Let $d$ be a natural
number and $N = 2^{d+1}$. For vectors $x, y \in \mathbb{C}^{2^d}$, write
$P_x = \sum_{j < 2^d} x_j X^j$ and $P_y = \sum_{j < 2^d} y_j X^j$, and let $x', y' \in \mathbb{C}^N$
be their zero paddings to length $N$ ($x'_j = x_j$ for $j < 2^d$ and $x'_j = 0$ otherwise, and
likewise for $y'$), with indices of $x'$ and $y'$ read modulo $N$. Then for every $k < N$, the
coefficient of $X^k$ in $P_x P_y$ equals

$$\sum_{j \in \mathbb{Z}/N\mathbb{Z}} x'_j \, y'_{k - j}.$$
