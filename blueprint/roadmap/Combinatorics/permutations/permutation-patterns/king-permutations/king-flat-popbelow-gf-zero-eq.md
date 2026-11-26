# Rational generating function for king permutations avoiding $P_1$

Let $P_1$ be the flat
partially ordered pattern of length $4$ whose first element lies below each of the other three,
and let $A_{P_1}(x; p, q, u, v)$ be the generating function of king permutations avoiding $P_1$,
in which $x$ marks length and $p$, $q$, $u$, $v$ mark ascents, descents, left-to-right maxima and
right-to-left maxima. Then $B \cdot A_{P_1} = A$ in $\mathbb{Z}[p, q, u, v][[x]]$, where
$A = \sum_{k=0}^{7} a_k x^k$ and $B = \sum_{k=0}^{7} b_k x^k$ with $a_0 = b_0 = -1$, $a_1 = -uv$,
$b_1 = 0$, $a_2 = b_2 = pqv$, $a_3 = pq^2v + pquv^2$, $b_3 = pq^2v$,
$a_4 = p^2q^2v^2 + pq^3v^2 + pq^2uv^2 - p^2qu^2v^2 - pq^2u^2v^2$, $b_4 = p^2q^2v^2 + pq^3v^2$,
$a_5 = p^2q^3v^2 - p^2q^2u^2v^2 + 2p^2q^3v^3 + pq^4v^3 - 2p^2q^2u^2v^3 - pq^3u^2v^3$,
$b_5 = p^2q^3v^2 + 2p^2q^3v^3 + pq^4v^3$,
$a_6 = 2p^2q^4v^3 - 2p^2q^3u^2v^3 + p^2q^4v^4 - p^2q^3u^2v^4$, $b_6 = 2p^2q^4v^3 + p^2q^4v^4$,
$a_7 = p^2q^5v^4 - p^2q^4u^2v^4$ and $b_7 = p^2q^5v^4$. Since $B$ has constant term $-1$, this
determines $A_{P_1} = A / B$.

## Sources

- Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*, INTEGERS 26 (2026), Article A59, Theorem 3.
