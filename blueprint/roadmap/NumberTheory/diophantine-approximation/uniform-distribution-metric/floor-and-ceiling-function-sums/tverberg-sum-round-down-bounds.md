# Sharp bounds for Tverberg's sum with rounding half down

Let $\ell \ge 2$ and let $F$ be
rounding to the nearest integer with ties rounded down, $F(y) = \lceil y - 1/2 \rceil$.
For integers $a_1, \dots, a_\ell$, a natural number $m$ and an integer $k$, let
$f(a, m, k) =
\sum_{U \subseteq \{1, \dots, \ell\}} (-1)^{\ell - |U|} F((k + \sum_{i \in U} a_i)/m)$
be Tverberg's sum of $F$, with $x/0 = 0$. Then $-2^{\ell-2} \le f(a, m, k) \le 2^{\ell-2}$ for
all such $a$, $m$ and $k$. Both bounds are attained: for every integer $r \ge 1$, if $a_i = r$
for all $i$ and $m = 2r$, then $f(a, m, 0) = (-1)^{\ell} 2^{\ell-2}$ and
$f(a, m, r) = (-1)^{\ell+1} 2^{\ell-2}$.

The paper states the equality cases separately for odd and even $\ell$.

## Sources

- Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam, *Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer Functions*, INTEGERS 25 (2025), Article A45, Theorem 6.
