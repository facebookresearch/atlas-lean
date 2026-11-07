# Generalized Pell matrix as a Riordan array

Let $k \ge 2$ be a natural number and let
$p(n, m)$, for natural numbers $n$ and $m$, be natural numbers such that for every $n$ the power
series $\sum_{m \ge 0} p(n, m)\, x^m$ over $\mathbb{Q}$ satisfies
$\left(\sum_{m \ge 0} p(n, m)\, x^m\right)(1 - x)^{n+1} = (1 + x + \dots + x^k)^n$. Then for all
natural numbers $n$ and $m$, the coefficient of $x^n$ in
$\frac{1}{1-x} \left(\frac{x(1 + x + \dots + x^k)}{1-x}\right)^m$ is $p(m, n - m)$ if $m \le n$
and $0$ otherwise. That is, the lower-triangular matrix whose entry in row $n$ and column $m$
is $p(m, n - m)$ is the Riordan array
$\left(\frac{1}{1-x}, \frac{x(1 + x + \dots + x^k)}{1-x}\right)$.

## Sources

- Jhon J. Bravo, Jose L. Herrera, and José L. Ramírez, "Combinatorial Interpretation of Generalized Pell Numbers," Journal of Integer Sequences 23 (2020), Article 20.2.1, Theorem (label Riordan), lines 269–272, https://cs.uwaterloo.ca/journals/JIS/VOL23/Bravo/bravo4.tex It follows from `pell_riordan_general`; the hypothesis `hk` is unused and keeps the source's shape. Proves `Wanted` entry `pell_riordan`.
