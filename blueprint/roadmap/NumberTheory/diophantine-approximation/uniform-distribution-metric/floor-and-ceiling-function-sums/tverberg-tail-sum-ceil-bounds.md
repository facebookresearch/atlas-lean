# Bounds for tail sums of Tverberg's ceiling sum

Let $\ell \ge 2$. For a tuple
$a = (a_1, \dots, a_\ell)$ of integers and natural numbers $m, K$, let
$T(a, m, K) = \sum_{k=1}^{K} f^{(\lceil \cdot \rceil)}(a, m, k)$, where $f^{(\lceil \cdot \rceil)}$
is Tverberg's sum with $F$ the ceiling function. Then
$-2^{\ell-2} \lfloor m/2 \rfloor \le T(a, m, K) \le 2^{\ell-2} \lfloor m/2 \rfloor$ for all such
$a, m, K$. Moreover, for every natural number $r$, if $a_i = r$ for every $i$, then
$T(a, 2r, r) = (-1)^\ell \, 2^{\ell-2} \, r$.

Theorem 8 as recorded asserts this equality for every $K$, which is false: for $\ell = 3$, $m = 2$,
$a_i = 1$ and $K = 2$ the sum is $0$, not $-2$. The paper's proof establishes it at $K = m/2$,
which is what is stated here.

## Sources

- Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam, *Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer Functions*, INTEGERS 25 (2025), Article A45, Theorem 8.
