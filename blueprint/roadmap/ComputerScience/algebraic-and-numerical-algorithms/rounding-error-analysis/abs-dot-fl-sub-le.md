# Forward error of the floating-point dot product

Let $K$ be a linearly ordered field with a floor function (for instance $\mathbb{Q}$ or $\mathbb{R}$) and $p$ a natural number. Write $\mathrm{fl}$ for rounding to nearest, ties to even, to binary floating-point numbers with $p$-bit significands and unbounded exponent, $u = 2^{-p}$ for the unit roundoff and $\gamma_k = k u / (1 - k u)$. Let $p \ge 1$, let $x, y$ be sequences in $K$ and let $n$ be a natural number with $n u < 1$. The floating-point dot product $\hat s = \hat s_n$, defined by $\hat s_0 = 0$ and $\hat s_{k+1} = \mathrm{fl}(\hat s_k + \mathrm{fl}(x_k y_k))$ (rounded products added from left to right, each addition rounded), satisfies

$$\Big|\hat s - \sum_{i<n} x_i y_i\Big| \le \gamma_n \sum_{i<n} |x_i y_i|.$$

For $n = 0$ both sides are $0$.

J. W. Demmel's Math 221 course (UC Berkeley, Lecture 5 notes, 2024, recalling homework 1.10) uses this bound, in its first-order form $n u \sum |x_i y_i|$, for matrix multiplication and for the backward error analysis of LU factorization. The exact form with $\gamma_n$ is the standard one of N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002. The relative error is small when there is little cancellation, that is when $|\sum x_i y_i|$ is comparable to $\sum |x_i y_i|$.

**Proof.** By induction on $n$. The first partial sum is the single rounding $\mathrm{fl}(x_0 y_0)$, since adding it to $0$ is exact, and $u \le \gamma_1$. If the partial sum $\hat s_k$ of $k \ge 1$ terms has error $e_k$ with $|e_k| \le \gamma_k T_k$, $T_k = \sum_{i<k} |x_i y_i|$, then $\hat s_{k+1} = \mathrm{fl}(\hat s_k + \mathrm{fl}(x_k y_k))$ has error at most $(u + (1 + u)\gamma_k) T_k + (2u + u^2)|x_k y_k| \le \gamma_{k+1} T_{k+1}$.

## Informally uses

- [The unit-roundoff bound](../floating-point-rounding/abs-fl-sub-le.md): every rounding has relative error at most $u$.
- [Floating-point numbers round to themselves](../floating-point-rounding/fl-eq-self.md): the first addition, to $0$, is exact.
- [Growth of $\gamma$ by one rounding](gamma-step.md) and [two roundings stay within $\gamma_{k+1}$](two-mul-add-sq-le-gamma.md): the induction step.
