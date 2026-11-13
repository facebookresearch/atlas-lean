# Higher $a$-numbers as sums of floors and of $\delta$

Let $p$ be a prime, let $d$ be a
natural number dividing $p - 1$, let $r$ and $n$ be natural numbers, let $\tau = (p + 1)/d$ and
$\gamma = ((p - 1) r + (p + 1))/d$, let $\delta$ be the rounding indicator for $p$ and $d$, and let
$A_r(n)$ be the lattice-point count for the $r$-th higher $a$-number at level $n$. Put
$t_n = \lfloor \gamma^{-1} p^n \rfloor$ and $s_n = \lfloor \tau^{-1} p^n \rfloor$. Then

$$A_r(n) = \sum_{i=1}^{t_n} (\gamma - \tau) i +
\sum_{i=t_n+1}^{s_n} (p^n - \lfloor \tau i \rfloor) - \sum_{i=t_n+1}^{s_n} \delta(i)$$

and

$$A_r(n) = \left(\sum_{i=1}^{s_n} (p^n - \lfloor \tau i \rfloor) -
\sum_{i=1}^{t_n} (p^n - \lfloor \gamma i \rfloor)\right) -
\left(\sum_{i=1}^{s_n} \delta(i) - \sum_{i=1}^{t_n} \delta(i)\right).$$

## Sources

- Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu, *Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Proposition 3.
