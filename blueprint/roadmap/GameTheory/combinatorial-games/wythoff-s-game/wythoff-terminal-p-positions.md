# P-positions of Wythoff's game with terminal positions

Let $\ell \ge 1$. Let $a_n$ be the
least natural number $m > \ell$ with $m \ne a_i$ and $m \ne b_i$ for all $i < n$, where
$b_i = a_i + i + \ell + 1$. Let $P$ be the set of positions $(x, y)$ with $x + y \le \ell$,
together with the pairs $(a_n, b_n)$ and $(b_n, a_n)$ for $n \ge 0$. Then $P$ is stable, meaning
no move of $K^\ell$ leads from a position of $P$ to a position of $P$, and absorbing, meaning
from every position outside $P$ some move of $K^\ell$ leads into $P$.

Since the move relation is well founded, a stable and absorbing set is the set of P-positions,
so the non-terminal P-positions of $K^\ell$ are exactly the pairs $(a_n, b_n)$ and $(b_n, a_n)$.

## Sources

- Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6, Theorem 17 (`jis-2026-26.1.6-thm-17`).
