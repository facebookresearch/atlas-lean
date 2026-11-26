# Diagonal slice function of a Toeplitz matrix

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and $k \in \mathbb{Z}$. The diagonal slice of index $k$ sends a sequence $x : \mathbb{N} \to \mathbb{K}$ to the sequence $\sigma_k x$ with

$$
(\sigma_k x)_i = \begin{cases} x_{i-k}, & k \le i, \\ 0, & k > i, \end{cases}
$$

shifting the coordinates by $k$ and killing those that fall off the end. For $k \ge 0$ this is the $k$-fold forward shift; for $k < 0$ it is the $|k|$-fold backward shift, $(\sigma_k x)_i = x_{i + |k|}$.
