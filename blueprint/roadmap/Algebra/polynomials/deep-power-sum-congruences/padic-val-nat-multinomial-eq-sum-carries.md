# Kummer's theorem for multinomial coefficients

Let $p$ be a prime and let
$r_1, \dots, r_k$ be natural numbers with sum $m$. For $i \ge 1$ let
$c_i = \lfloor ((r_1 \bmod p^i) + \dots + (r_k \bmod p^i)) / p^i \rfloor$. Then

$$v_p\binom{m}{r_1, \dots, r_k} = \sum_{i=1}^{m} c_i.$$

Here $c_i$ is the carry into digit position $i$ when $r_1 + \dots + r_k$ is added in base $p$, and
$c_i = 0$ for $i > m$, so the right side is the sum of all the carries.

## Sources

- S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum Congruences*, INTEGERS 24 (2024), Article A46, Theorem 23 (`integers-2024-A46-thm-23`).
