# Descartes' circle theorem

Let four circles in the Euclidean plane have centers $c_i$ and
radii $r_i > 0$ for $i = 1, 2, 3, 4$, let $d$ be the Euclidean distance, and let
$k_1, k_2, k_3, k_4$ be real numbers. Suppose that either
(a) any two of the circles are externally tangent, $d(c_i, c_j) = r_i + r_j$ for $i \ne j$, and
$k_i = 1/r_i$ for every $i$; or
(b) for some index $e$, each other circle is internally tangent to circle $e$, that is,
$d(c_e, c_j) = r_e - r_j$ for $j \ne e$; any two circles other than circle $e$ are externally
tangent, $d(c_i, c_j) = r_i + r_j$ for distinct $i, j \ne e$; and $k_e = -1/r_e$ and
$k_j = 1/r_j$ for $j \ne e$.
Then $(k_1 + k_2 + k_3 + k_4)^2 = 2(k_1^2 + k_2^2 + k_3^2 + k_4^2)$.

Proof: Following the Cayley-Menger/Gram-determinant argument in Lagarias, Mallows, and Wilks,
*Beyond the Descartes circle theorem*, Section 3, and Wikipedia's proof sketch, introduce signed
radii, expand the planar Gram determinant in coordinates, and clear denominators.

The theorem is stated for circles of positive radius only; Descartes configurations containing a line (curvature
$0$), such as the strip packing $(0, 0, 1, 1)$, are outside its scope, although the algebraic consequences in the
[Apollonian group](apollonian-group/README.md) topic allow zero entries.

## Related topics

- [Apollonian group](apollonian-group/README.md): the curvature quadruples of Descartes configurations and the
  reflections that generate Apollonian packings.
- [Complex Descartes theorem](apollonian-circle-packings/complex-descartes-theorem.md): the same relation for the
  products curvature × center.

## Sources

- J. C. Lagarias, C. L. Mallows and A. R. Wilks, *Beyond the Descartes circle theorem*, Amer. Math. Monthly 109 (2002) 338–361, arXiv:math/0101066v1, Theorem 1.1.
- https://en.wikipedia.org/wiki/Descartes%27_theorem.
