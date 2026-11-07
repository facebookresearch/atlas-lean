# Monge's three-circle theorem

Let $c_1, c_2, c_3$ be points of the Euclidean plane
$\mathbb{R}^2$ and let $r_1, r_2, r_3$ be pairwise distinct positive real numbers such that the
closed disks of radius $r_i$ centered at $c_i$ are pairwise disjoint. Then the external homothety
centers $(r_1 - r_2)^{-1}(r_1 c_2 - r_2 c_1)$, $(r_2 - r_3)^{-1}(r_2 c_3 - r_3 c_2)$ and
$(r_1 - r_3)^{-1}(r_1 c_3 - r_3 c_1)$ of the three pairs of circles are collinear.

## Sources

- https://en.wikipedia.org/wiki/Monge%27s_theorem. The source's hypothesis is that no circle lies inside another; the pairwise disjointness of the closed disks (`hd12`, `hd23`, `hd13`) is stronger. Omitted source case: the source also treats two circles of equal radius, whose external tangents are parallel and meet at a point at infinity. The distinct-radii hypotheses `h12`, `h23`, `h13` exclude it, and the affine formula for the centers cannot express it. It follows from `monge_three_circles_general`; the positivity hypotheses `hr₁`, `hr₂`, `hr₃` and the disjointness hypotheses are unused and keep the `Wanted` statement's shape.
