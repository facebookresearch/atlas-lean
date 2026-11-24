# Correctness of ANY-SEGMENTS-INTERSECT

Let $\Bbbk$ be a linearly ordered field and let
$s_0, \dots, s_{n-1}$ be closed segments in $\Bbbk^2$, each given by its two endpoints in either
order. Suppose no segment is vertical (its two endpoints have different $x$-coordinates) and no
point lies on three segments $s_i$, $s_j$, $s_k$ with $i$, $j$, $k$ pairwise distinct. Then
ANY-SEGMENTS-INTERSECT returns true on these segments if and only if there are indices $i \ne j$
such that $s_i$ and $s_j$ intersect (CLRS, third edition, Theorem 33.1).
