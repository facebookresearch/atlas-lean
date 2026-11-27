# The constant $\gamma_n$ of rounding error analysis

Let $K$ be a linearly ordered field with a floor function, $p$ a natural number and $u = 2^{-p}$ the unit roundoff. For a natural number $n$,

$$\gamma_n = \frac{n u}{1 - n u} \in K,$$

with the convention that division by $0$ gives $0$, so $\gamma_n = 0$ when $n u = 1$; $\gamma_n$ is negative when $n u > 1$, and $\gamma_0 = 0$.

When $n u < 1$, $\gamma_n$ bounds the accumulated relative error of $n$ roundings: $\prod_{i=1}^n (1 + \delta_i)$ with $|\delta_i| \le u$ lies in $[1 - \gamma_n, 1 + \gamma_n]$.
