# Floating-point evaluation of $c - \sum_{k<m} a_k b_k$

Let $K$ be a linearly ordered field with a floor function (for instance $\mathbb{Q}$ or $\mathbb{R}$) and $p$ a natural number. Write $\mathrm{fl}$ for rounding to nearest, ties to even, to binary floating-point numbers with $p$-bit significands and unbounded exponent. For $c \in K$ and sequences $a, b$ in $K$, the floating-point evaluation of $c - \sum_{k<m} a_k b_k$ is the value $\hat s_m$ of the recurrence

$$\hat s_0 = c, \qquad \hat s_{k+1} = \mathrm{fl}\big(\hat s_k - \mathrm{fl}(a_k b_k)\big):$$

starting from $c$, not rounded, the rounded products are subtracted from left to right, rounding each subtraction. For $m = 0$ the value is $c$ itself.
