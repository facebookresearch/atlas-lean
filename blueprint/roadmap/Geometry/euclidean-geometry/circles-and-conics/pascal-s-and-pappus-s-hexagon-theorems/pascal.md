# Pascal's theorem for real projective conics

Let $M$ be a real symmetric $3 \times 3$
matrix with $\det M \ne 0$, and let $a_1, a_2, a_3, b_1, b_2, b_3 \in \mathbb{R}^3$ be nonzero
vectors on the conic $x^\top M x = 0$, no two of which represent the same projective point.
Writing $\cdot$ and $\times$ for the dot and cross products on $\mathbb{R}^3$, let
$p = (a_1 \times b_2) \times (a_2 \times b_1)$, $q = (a_1 \times b_3) \times (a_3 \times b_1)$ and
$r = (a_2 \times b_3) \times (a_3 \times b_2)$ be the meets of the opposite sides of the hexagon
$a_1 b_2 a_3 b_1 a_2 b_3$. Then $p$, $q$ and $r$ are collinear: $p \cdot (q \times r) = 0$.

## Sources

- B. Pascal, *Essay pour les coniques* (1640). Knill, *Some fundamental theorems in mathematics*, §146. Problem `pascal` of the lean-eval benchmark.
