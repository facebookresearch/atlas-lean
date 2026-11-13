# Essential dimension of the symmetric group on five letters

Write
$\operatorname{ed}(S_n)$ for the essential dimension of the symmetric group $S_n$ over
$\mathbb{C}$ in the general-polynomial sense: the least transcendence degree over $\mathbb{C}$
of a subfield $F_0$ of the coefficient field $\mathbb{C}(a_1, \dots, a_n)$ of the general
polynomial of degree $n$ over which that polynomial descends up to Tschirnhaus transformation.
Then $\operatorname{ed}(S_5) = 2$.

## Sources

- Buhler--Reichstein (1997), exact value `ed_ℂ(S₅) = 2`: their general bounds `⌊5/2⌋ ≤ ed_ℂ(S₅) ≤ 5 - 3` coincide at `2`. The classical Bring--Jerrard form `X^5 + pX + q` is not the descent behind that upper bound here: producing it already requires solving auxiliary equations over an extension of the coefficient field, and normalizing further to `X^5 + X + a` is again only a scaling over an extension, so neither form witnesses a descent over the original field in the sense of this file (in particular nothing here implies `edSn 5 ≤ 1`).
