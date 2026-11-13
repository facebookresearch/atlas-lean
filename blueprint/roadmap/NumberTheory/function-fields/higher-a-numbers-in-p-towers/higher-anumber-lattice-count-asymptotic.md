# Asymptotic formula for higher $a$-numbers

Let $p$ be a prime, let $d$ be a natural number
dividing $p - 1$, let $r \ge 1$, and for each natural number $n$ let $A_r(n)$ be the lattice-point
count for the $r$-th higher $a$-number at level $n$. Let $D_r$ be the prime-to-$p$ part of the
denominator of $d/((p - 1) r + (p + 1))$, and let
$M_r = \operatorname{lcm}(2, \operatorname{ord}_{D_r} p)$, where $\operatorname{ord}_{D_r} p$ is
the multiplicative order of $p$ modulo $D_r$. Then there are a positive integer $N_r$, a rational
number $\lambda_r$ and a function $\nu_r$ from the natural numbers to the rationals such that
$\nu_r(n + M_r) = \nu_r(n)$ for every $n \ge N_r$, and

$$A_r(n) = \frac{r}{r + (p + 1)/(p - 1)} \cdot \frac{d}{2(p + 1)} \cdot p^{2n} + \lambda_r n +
\nu_r(n)$$

for every $n \ge N_r$.

By Theorem 1 of the source, $A_r(n)$ is the higher $a$-number $a^r(X_n)$ of the $n$-th layer of
a $\mathbb{Z}_p$-tower with minimal break ratios and ramification invariant $d$; the source
states the periodicity as: the minimal period of $\nu_r$ divides $M_r$.

## Sources

- Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu, *Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Theorem 2.
