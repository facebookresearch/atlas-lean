# Back substitution in floating point

Let $K$ be a linearly ordered field with a floor function (for instance $\mathbb{Q}$ or $\mathbb{R}$) and $p$ a natural number. Write $\mathrm{fl}$ for rounding to nearest, ties to even, to binary floating-point numbers with $p$-bit significands and unbounded exponent. Let $U$ be an $n \times n$ matrix over $K$ and $y, x \in K^n$. The vector $x$ is computed from $U$ and $y$ by back substitution in floating point when, for every $i < n$,

$$x_i = \mathrm{fl}\big(\hat t^{(i)} / U_{ii}\big),$$

where $\hat t^{(i)}$ is obtained from $y_i$ (not rounded) by subtracting the rounded products $\mathrm{fl}(U_{ik}\, x_k)$ for $k = n - 1, n - 2, \dots, i + 1$, in this order, rounding each subtraction. In particular $x_{n-1} = \mathrm{fl}(y_{n-1} / U_{n-1,n-1})$.

Equivalently, reversing the order of rows, columns and entries ($i \mapsto n - 1 - i$), $x$ is computed by [forward substitution](is-fl-lower-solve.md) from the reversed matrix and right-hand side. The condition involves only the entries $U_{ik}$ with $k \ge i$; a division by $0$ gives $0$.
