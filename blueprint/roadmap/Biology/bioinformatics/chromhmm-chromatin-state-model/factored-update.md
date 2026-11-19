# Factored per-mark update

For real weights $c$ on $\{0, 1\}^d$ and a mark $j$, the factored update is

$$\hat p_j = \frac{n_1(c, j)}{n_1(c, j) + n_0(c, j)},$$

where $n_1$ and $n_0$ are the weights with [mark present](ones-count.md) and [absent](zeros-count.md), with the convention $x/0 = 0$.
