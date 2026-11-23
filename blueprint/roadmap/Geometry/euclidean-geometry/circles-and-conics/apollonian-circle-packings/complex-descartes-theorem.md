# Complex Descartes theorem

Let four circles in the plane $\mathbb{C}$ have centers $c_i$, radii $r_i > 0$ and signed curvatures $k_i$, in
either configuration of Descartes' circle theorem: (a) pairwise externally tangent, $|c_i - c_j| = r_i + r_j$, with
$k_i = 1/r_i$; or (b) one circle $e$ internally tangent to the three others, $|c_e - c_j| = r_e - r_j$, which are
pairwise externally tangent, with $k_e = -1/r_e$ and $k_j = 1/r_j$ for $j \ne e$. Then the products $k_i c_i$ of
curvature and center satisfy the same relation as the curvatures:

$$\Big(\sum_{i=1}^4 k_i c_i\Big)^2 = 2 \sum_{i=1}^4 (k_i c_i)^2 \quad \text{in } \mathbb{C}.$$

Lagarias, Mallows and Wilks state it for all Descartes configurations, lines included (with a suitable convention for
$k_i c_i$ on a line); the statement above keeps the two configurations of
[Descartes' circle theorem](../descartes-circle-theorem.md) and follows from the
[version for signed radii](complex-descartes-of-signed.md). Replacing $c_i$ by $c_i + w$ and comparing coefficients of
$w$ gives the real Descartes relation and the mixed relation $\sum k_i (k_i c_i) = \tfrac12 (\sum k_i)(\sum k_i c_i)$
(their equation (2.3)). Lagarias, Mallows and Wilks also show, through the curvature-center coordinates of their
Section 3, that the products curvature × center transform under the Apollonian group like the curvatures.
Example: in the configuration $(-1, 2, 2, 3)$ with bounding circle of radius $1$ centred at $0$, the products are
$(0, 1, -1, 2i)$, and $(2i)^2 = -4 = 2(0 + 1 + 1 - 4)$.

## Sources

- J. C. Lagarias, C. L. Mallows and A. R. Wilks, *Beyond the Descartes circle theorem*, Amer. Math. Monthly 109 (2002) 338–361, arXiv:math/0101066v1, Theorem 2.1 and equation (2.3).
