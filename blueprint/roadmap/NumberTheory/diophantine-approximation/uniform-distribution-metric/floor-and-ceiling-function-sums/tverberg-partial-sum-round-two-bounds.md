# Bounds for partial Tverberg sums of two integers under rounding half up

Let
$r^+(y) = \lfloor y + 1/2 \rfloor$ be rounding to the nearest integer with ties rounded up. For
integers $a, b, k$ and a natural number $m$, let
$f(a, b; m, k) = r^+(k/m) - r^+((k + a)/m) - r^+((k + b)/m) + r^+((k + a + b)/m)$ be
Tverberg's sum of $r^+$ at $(a, b)$, with $x/0 = 0$. For all integers $a, b$ and natural
numbers $m, K$,
$-\lfloor m/2 \rfloor \le \sum_{k=0}^{K} f(a, b; m, k) \le \lfloor m/2 \rfloor$. The lower bound
is attained: for every natural number $r$,
$\sum_{k=0}^{r} f(r + 1, r + 1; 2(r + 1), k) = -(r + 1)$.

## Sources

- Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam, *Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer Functions*, INTEGERS 25 (2025), Article A45, Theorem 9.
