# Forward substitution in floating point

Let $K$ be a linearly ordered field with a floor function (for instance $\mathbb{Q}$ or $\mathbb{R}$) and $p$ a natural number. Write $\mathrm{fl}$ for rounding to nearest, ties to even, to binary floating-point numbers with $p$-bit significands and unbounded exponent. Let $L$ be an $n \times n$ matrix over $K$ and $b, y \in K^n$. The vector $y$ is computed from $L$ and $b$ by forward substitution in floating point when, for every $i < n$,

$$y_i = \mathrm{fl}\big(\hat s^{(i)}_i / L_{ii}\big),$$

where $\hat s^{(i)}_0 = b_i$ (not rounded) and $\hat s^{(i)}_{k+1} = \mathrm{fl}\big(\hat s^{(i)}_k - \mathrm{fl}(L_{ik}\, y_k)\big)$ for $k < i$: the products are rounded and subtracted one at a time, $k = 0, \dots, i - 1$, rounding each subtraction. In particular $y_0 = \mathrm{fl}(b_0 / L_{00})$.

The condition involves only the entries $L_{ik}$ with $k \le i$. It does not itself require $L$ to be triangular or its diagonal to be nonzero; a division by $0$ gives $0$.
