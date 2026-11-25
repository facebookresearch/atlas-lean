# Floating-point matrix product

Let $K$ be a linearly ordered field with a floor function (for instance $\mathbb{Q}$ or $\mathbb{R}$) and $p$ a natural number. Write $\mathrm{fl}$ for rounding to nearest, ties to even, to binary floating-point numbers with $p$-bit significands and unbounded exponent. For natural numbers $m, n, r$, an $m \times n$ matrix $A$ and an $n \times r$ matrix $B$ over $K$, the floating-point matrix product $\hat C$ is the $m \times r$ matrix whose entry $(i, j)$ is the [floating-point dot product](dot-fl.md) of row $i$ of $A$ and column $j$ of $B$:

$$\hat s_0 = 0, \qquad \hat s_{k+1} = \mathrm{fl}\big(\hat s_k + \mathrm{fl}(A_{ik} B_{kj})\big), \qquad \hat C_{ij} = \hat s_n,$$

the products being accumulated from $k = 0$ to $n - 1$. For $n = 0$, $\hat C$ is the zero matrix.
