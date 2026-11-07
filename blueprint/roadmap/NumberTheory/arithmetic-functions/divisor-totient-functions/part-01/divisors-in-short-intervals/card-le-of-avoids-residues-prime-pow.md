# Arithmetic large sieve with prime-power moduli

Let $N \ge 1$ be an integer and let $M$
be a finite set of integers contained in $[a, a + N)$ for some integer $a$. Let $S$ be a finite
set of primes and, for each $p \in S$, let $\beta_p \ge 1$ be an integer and let $\Omega_p$ be a
set of fewer than $p^{\beta_p}$ integers in $[0, p^{\beta_p})$ such that no $m \in M$ has its
remainder modulo $p^{\beta_p}$ in $\Omega_p$. Then for every real $Q \ge 1$,

$$|M| \le \frac{N + Q^2}{\sum_{1 \le q \le Q} h(q)},$$

where $q$ runs over the integers in $[1, Q]$ and $h(q) = \prod_{p \mid q} h_p(q)$, the product
over the prime factors $p$ of $q$ of $h_p(q) = |\Omega_p| / (p^{\beta_p} - |\Omega_p|)$ if
$p \in S$ and $p^{\beta_p}$ exactly divides $q$, and $h_p(q) = 0$ otherwise (so $h(1) = 1$).

## Sources

- Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026), Article A115, Lemma 3 (`integers-2026-A115-lem-3`).
