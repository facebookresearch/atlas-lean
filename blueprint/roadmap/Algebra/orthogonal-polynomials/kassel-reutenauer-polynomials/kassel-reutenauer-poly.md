# Kassel–Reutenauer polynomial

For a natural number $n$, the Kassel–Reutenauer polynomial
$\bar P_n(X) \in \mathbb{Z}[X]$ is defined by

$$
\bar P_n(X) = a_{n,0} + \sum_{i=1}^{n-1} a_{n,i} \, \bar T_i(X),
$$

where $a_{n,i}$ is the number of divisors $d$ of $n$ with $d(d - 2i) \le 2n$ and
$n < 2d(d - i)$ (equivalently, $(i + \sqrt{2n + i^2})/2 < d \le i + \sqrt{2n + i^2}$), and
$\bar T_i$ is the monic Chebyshev polynomial: $\bar T_0 = 2$, $\bar T_1 = X$ and
$\bar T_{i+2} = X \bar T_{i+1} - \bar T_i$. For $n = 0$ the sum is empty and the set of divisors
of $0$ is taken to be empty, so $\bar P_0 = 0$.

In the paper, $\bar P_n$ is characterized for $n \ge 1$ by
$\bar P_n(q + q^{-1}) = P_n(q)/q^{n-1}$, where $(q - 1)^2 P_n(q)$ is the number of ideals of
codimension $n$ of $\mathbb{F}_q[x, y, x^{-1}, y^{-1}]$; the definition here uses the explicit
expansion (2.4) of the paper instead.

## Sources

- C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.4, (2.1)–(2.4) and Table 2.
