# Interior step of the generalized hyperbolic Pascal triangle

Fix $q \in \mathbb{N}$ and a
type $R$ with an addition. A vertex is recorded as a pair $(c, x)$ of a type code $c \in \mathbb{N}$
(code $0$ for the wingers at the ends of a row, $1$ for type $A$ and $2$ for type $B$) and a
value $x \in R$. Given a list $v_0, v_1, \dots, v_m$ of such pairs with $m \ge 1$ and
$v_i = (c_i, x_i)$, the interior step lists, from left to right and for $i = 1, \dots, m$, the
type-$A$ vertex $(1, x_{i-1} + x_i)$, followed, when $i < m$, by $d_i$ copies of the type-$B$
vertex $(2, x_i)$, where $d_i = q - 4$ if $c_i = 1$ and $d_i = q - 3$ otherwise (both differences
truncated at $0$). A list with fewer than two entries gives the empty list.

## Sources

- Hacène Belbachir, Fella Rami, and László Szalay, *Alternating Sums in the Generalized Hyperbolic Pascal Triangle*, INTEGERS 24 (2024), Article A84, Section 1 (construction of the triangle linked to `{4, q}`).
