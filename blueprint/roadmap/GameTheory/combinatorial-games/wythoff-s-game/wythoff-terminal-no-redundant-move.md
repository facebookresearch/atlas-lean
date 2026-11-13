# No redundant move in $K^\ell$ for $1 \le \ell \le 4$

Let $1 \le \ell \le 4$. Let $a_n$ be
the least natural number $m > \ell$ with $m \ne a_i$ and $m \ne b_i$ for all $i < n$, where
$b_i = a_i + i + \ell + 1$, and let $P$ be the set of positions $(x, y)$ with $x + y \le \ell$
together with the pairs $(a_n, b_n)$ and $(b_n, a_n)$ for $n \ge 0$. Let $v$ be one of the move
vectors $(i, 0)$, $(0, i)$ or $(i, i)$ with $i > 0$. Then there is a position $p \notin P$ such
that every move of $K^\ell$ from $p$ to a position $q \in P$ satisfies $p = q + v$.

In other words, once the moves by $v$ are removed from $K^\ell$, the set $P$ is no longer
absorbing. Since $P$ is the set of P-positions of $K^\ell$ (Theorem 17) and stays stable when
moves are removed, removing the moves by $v$ changes the set of P-positions.

## Sources

- Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6, Theorem 30 (`jis-2026-26.1.6-thm-30`).
