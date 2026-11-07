# Tverberg's sum in terms of the inclusion-exclusion-like sum

Let $F$ be one of
$\lfloor \cdot \rfloor$, $\lceil \cdot \rceil$, $r^+(y) = \lfloor y + 1/2 \rfloor$ and
$r^-(y) = \lceil y - 1/2 \rceil$. For real numbers $x_1, \dots, x_n$ let
$g(x_1, \dots, x_n) =
\sum_{\emptyset \ne U \subseteq \{1, \dots, n\}} (-1)^{|U| - 1} F(\sum_{i \in U} x_i)$
be the inclusion-exclusion-like sum of $F$. For every natural number $\ell$, integers
$a_1, \dots, a_\ell$, a natural number $m$ and an integer $k$, let
$f(a, m, k) =
\sum_{U \subseteq \{1, \dots, \ell\}} (-1)^{\ell - |U|} F((k + \sum_{i \in U} a_i)/m)$
be Tverberg's sum of $F$, with $x/0 = 0$. Then
$f(a, m, 0) = (-1)^{\ell+1} g(a_1/m, \dots, a_\ell/m)$ and
$f(a, m, k) = (-1)^{\ell} g(a_1/m, \dots, a_\ell/m, k/m) + (-1)^{\ell+1} g(a_1/m, \dots, a_\ell/m)$.

The paper assumes $\ell \ge 2$ and $m \ge 1$; the identities hold without these hypotheses.

## Sources

- Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam, *Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer Functions*, INTEGERS 25 (2025), Article A45, Lemma 2.
