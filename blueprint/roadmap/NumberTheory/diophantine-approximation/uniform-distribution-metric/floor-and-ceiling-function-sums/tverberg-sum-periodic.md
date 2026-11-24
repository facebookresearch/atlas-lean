# Periodicity of Tverberg's sum

Let $\ell \ge 2$ and let $F$ be one of
$\lfloor \cdot \rfloor$, $\lceil \cdot \rceil$, $r^+(y) = \lfloor y + 1/2 \rfloor$ and
$r^-(y) = \lceil y - 1/2 \rceil$.
For integers $a_1, \dots, a_\ell$, a natural number $m$ and an integer $k$, let
$f(a, m, k) =
\sum_{U \subseteq \{1, \dots, \ell\}} (-1)^{\ell - |U|} F((k + \sum_{i \in U} a_i)/m)$
be Tverberg's sum of $F$, with $x/0 = 0$. For every index $i$ and every integer $q$, replacing
$a_i$ by $a_i + q m$ does not change $f(a, m, k)$, and $f(a, m, k + q m) = f(a, m, k)$.

The hypothesis $\ell \ge 2$ is needed: for $\ell = 1$, $F = \lfloor \cdot \rfloor$ and $m \ge 1$,
$f((a), m, k) = \lfloor (k + a)/m \rfloor - \lfloor k/m \rfloor$ increases by $q$ when $a$ is
replaced by $a + q m$.

## Sources

- Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam, *Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer Functions*, INTEGERS 25 (2025), Article A45, Lemma 3.
