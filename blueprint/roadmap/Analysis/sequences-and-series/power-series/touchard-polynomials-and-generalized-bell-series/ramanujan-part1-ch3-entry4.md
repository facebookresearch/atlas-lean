# Exponential generating function of Ramanujan's Bell-type series (Entry 4)

Let $F$ be
Ramanujan's generalized Bell function. For all complex numbers $a$ and $x$, let
$f(x, n) = F(0, 1, x; n) = e^{-x} \sum_{j=0}^{\infty} \frac{(j+1)^n x^{j+1}}{j!}$ for natural
numbers $n$, and set $f(x, -1) = 1$. Then the series
$\sum_{n=0}^{\infty} \frac{a^n}{n!} f(x, n-1)$ converges absolutely and its sum is
$e^{x(e^a - 1)}$.

## Sources

- Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 4, formula (4.1), printed pp. 47--48 / PDF pp. 57--58. Proves `Wanted` entry `ramanujan_part1_ch3_entry4`. The source's `f(x, n) = e^{-x} ∑_{j ≥ 0} (j + 1)ⁿ xʲ⁺¹ / j!` is `generalizedBellGenerating 0 1 x n`.
