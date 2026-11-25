# Hybrid bound for prime divisors of $x^p - 1$

Let $p$ be a prime, let $x > 1$ be a natural
number, and let $\omega_p$ be the number of distinct prime factors of $x^p - 1$. List the primes
$\rho \not\equiv 1 \pmod p$ in increasing order as $r_{0,0} < r_{1,0} < \cdots$ and the primes
$\rho \equiv 1 \pmod p$ as $r_{0,1} < r_{1,1} < \cdots$. Then there is $k < \omega_p$ such that
$r_{0,0}, \dots, r_{k-1,0}$ exist and

$$1 + \prod_{i < k} r_{i,0} \le x \qquad\text{and}\qquad
1 + \prod_{i < k} r_{i,0} \prod_{j < \omega_p - k} r_{j,1} \le x^p.$$

(For odd $p$ there are infinitely many primes $\rho \not\equiv 1 \pmod p$; for $p = 2$ the only
one is $2$, so then $k \le 1$.) This is the case $n = p$ of the source's Theorem 1, which its
Proposition 2 states as $x \ge \min_{0 \le k < \omega_p} \max\bigl(1 + \prod_{i \le k} r_{i,0},
(1 + \prod_{i \le k} r_{i,0} \prod_{j \le \omega_p - k} r_{j,1})^{1/p}\bigr)$ with primes indexed
from $1$; raising the second bound to the $p$-th power gives the form above.

## Sources

- Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026), Article A95, Proposition 2.
