# Ramified bound on prime divisors of $x^p - 1$ for prime $p$

Let $p$ be a prime, let $x > 1$ be a natural number, and let
$\omega_p$ be the number of distinct prime factors of $x^p - 1$. List the primes
$\rho \not\equiv 1 \pmod p$ in increasing order as $r_{0,0} < r_{1,0} < \cdots$ and the primes
$\rho \equiv 1 \pmod p$ as $r_{0,1} < r_{1,1} < \cdots$, let $b$ be the index with $r_{b,0} = p$,
and put $R^0_k = \prod_{i < k} r_{i,0}$, $S^0_k = \prod_{i \le k,\, i \ne b} r_{i,0}$ (for $k \ge b$
this is $p^{-1} R^0_{k+1}$) and $R^1_k = \prod_{j < \omega_p - k} r_{j,1}$.

- If $p \nmid x^p - 1$, there is $k < \omega_p$ such that either $k \le b$, $1 + R^0_k \le x$
  and $1 + R^0_k R^1_k \le x^p$, or $k > b$, $1 + S^0_k \le x$ and $1 + S^0_k R^1_k \le x^p$.
- If $p$ is odd and $p \mid x^p - 1$, there is $k$ with $0 < k < \omega_p$ such that either
  $k \le b$, $1 + p R^0_{k-1} \le x$ and $1 + p^2 R^0_{k-1} R^1_k \le x^p$, or $k > b$,
  $1 + R^0_k \le x$ and $1 + p R^0_k R^1_k \le x^p$.

In each case the primes $r_{i,0}$ in these products exist; this restricts $k$ only for $p = 2$,
where $2$ is the only prime $\not\equiv 1 \pmod 2$.

This is the case $n = p$ of the source's Theorem 2 (its Proposition 3): its minima over
$k \in [0, k') \cup [k', \omega_p)$, with $k' = b + 1$, are stated above as the existence of $k$,
and its second bounds are raised to the $p$-th power. The divisible case needs $p \ne 2$ and
$k > 0$: $R^0_{-1}$ is undefined at $k = 0$, and for $p = 2$ and $x = 3$ (so $x^2 - 1 = 8$ and
$\omega_2 = 1$) the only possible $k = 0$ fails under any reading (with $R^0_{-1} = 1$ the second
bound reads $1 + 4 \cdot 3 = 13 \le 9$).

## Sources

- Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026), Article A95, Proposition 3.
