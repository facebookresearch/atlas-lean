# Indicator encoding of a censored observation on a grid

Let $t_0, \dots, t_{k-1}$ be real numbers (the grid). An observation is a pair $o = (T, \delta) \in \mathbb R \times \mathbb R$. Its indicator encoding is the vector of the Euclidean space $\mathbb R^{2k}$ indexed by death coordinates $(\mathrm{death}, j)$ and at-risk coordinates $(\mathrm{risk}, j)$, $j \in \{0, \dots, k - 1\}$, with

$$\mathrm{enc}_t(o)_{(\mathrm{death}, j)} = \mathbf 1\{o = (t_j, 1)\}, \qquad \mathrm{enc}_t(o)_{(\mathrm{risk}, j)} = \mathbf 1\{t_j \le T\}.$$

The death coordinate at $t_j$ is $1$ exactly when the observed time is $t_j$ and $\delta = 1$; the at-risk coordinate at $t_j$ is $1$ exactly when the observed time is at least $t_j$. See the [coordinate space](coord.md).
