# Residual bound for one division step

Let $K$ be a linearly ordered field with a floor function (for instance $\mathbb{Q}$ or $\mathbb{R}$) and $p$ a natural number. Write $\mathrm{fl}$ for rounding to nearest, ties to even, to binary floating-point numbers with $p$-bit significands and unbounded exponent, $u = 2^{-p}$ for the unit roundoff and $\gamma_k = k u / (1 - k u)$. For $c \in K$ and sequences $a, b$ in $K$, the floating-point value of $c - \sum_{k<m} a_k b_k$ is $\hat s_m$, where $\hat s_0 = c$ (not rounded) and $\hat s_{k+1} = \mathrm{fl}(\hat s_k - \mathrm{fl}(a_k b_k))$. Let $d \in K$ be nonzero, let $(m + 1) u < 1$ and let $\hat z = \mathrm{fl}(\hat s_m / d)$. Then

$$\Big|c - \sum_{k<m} a_k b_k - d\,\hat z\Big| \le \gamma_{m+1} \Big(\sum_{k<m} |a_k b_k| + |d\,\hat z|\Big).$$

This is one step of forward substitution, and of the computation of an entry of $\hat L$ in Gaussian elimination.

## Informally uses

- [Error of a floating-point $c - \sum a_k b_k$, measured by the result](abs-sub-dot-fl-add-sum-sub-le.md): the subtractions.
- [Rounding error relative to the rounded value](abs-fl-sub-le-gamma-one-mul.md) and [composition of relative errors](one-add-gamma-mul-le.md): the division.
