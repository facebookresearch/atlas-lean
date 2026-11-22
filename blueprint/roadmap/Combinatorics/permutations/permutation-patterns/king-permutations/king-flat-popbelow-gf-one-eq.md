# Rational generating function for king permutations avoiding $P_2$

Let $P_2$ be the flat
partially ordered pattern of length $4$ whose second element lies below each of the other three,
and let $A_{P_2}(x; p, q, u, v)$ be the generating function of king permutations avoiding $P_2$,
in which $x$ marks length and $p$, $q$, $u$, $v$ mark ascents, descents, left-to-right maxima and
right-to-left maxima. Then $B \cdot A_{P_2} = A$ in $\mathbb{Z}[p, q, u, v][[x]]$, where
$A = \sum_{k=0}^{6} a_k x^k$ and $B = \sum_{k=0}^{6} b_k x^k$ with $a_0 = b_0 = -1$, $a_1 = -uv$,
$b_1 = 0$, $a_2 = b_2 = pqu + pquv$, $a_3 = p^2quv + pqu^2v + pqu^2v^2$, $b_3 = p^2quv$,
$a_4 = b_4 = p^2q^2uv + p^3qu^2v - p^2q^2u^2v + p^2q^2uv^2$,
$a_5 = p^3q^2u^2v + p^2q^3uv^2 + p^3q^2u^2v^2 - p^2q^2u^3v^2$,
$b_5 = p^3q^2u^2v + p^2q^3uv^2 + p^3q^2u^2v^2$ and $a_6 = b_6 = p^3q^3u^2v^2$. Since $B$ has
constant term $-1$, this determines $A_{P_2} = A / B$.

## Sources

- Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*, INTEGERS 26 (2026), Article A59, Theorem 4.
