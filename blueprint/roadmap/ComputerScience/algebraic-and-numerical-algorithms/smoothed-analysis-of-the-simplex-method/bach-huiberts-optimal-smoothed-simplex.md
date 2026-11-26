# Bach-Huiberts optimal noise dependence for the smoothed simplex method

There is a simplex method whose smoothed complexity on linear programs with $d$ variables and $n$ constraints is

$$
O\!\left(\sigma^{-1/2} d^{11/4} \log(n)^{7/4}\right)
$$

pivot steps. Conversely, for small $\sigma$ there are base programs with $n = \lfloor (4/\sigma)^d \rfloor$ constraints whose smoothed feasible polyhedron has, with high probability, combinatorial diameter

$$
\Omega\!\left(\sigma^{-1/2} d^{1/2} \ln(4/\sigma)^{-1/4}\right) ,
$$

so no simplex method can have smoothed complexity with better noise dependence than $\sigma^{-1/2}$, up to polylogarithmic factors.

## Proof sketch

The upper bound designs the pivot path more carefully than a single shadow path, so that its expected length is controlled through the edge-counting analysis of two-dimensional sections with only a $\sigma^{-1/2}$ loss. For the lower bound, taking $(4/\sigma)^d$ constraints whose normals are dense on the sphere makes the smoothed feasible region approximate a ball, and each edge of the polyhedron then turns the normal direction by only about $\sigma^{1/2}$, so connecting antipodal vertices requires $\Omega(\sigma^{-1/2})$ edges up to the stated factors; a lower bound on the combinatorial diameter bounds every simplex method from a suitable starting vertex.

## Depends on

- [Huiberts-Lee-Zhang smoothed complexity O(sigma^{-3/2} d^{13/4} log^{7/4} n)](huiberts-lee-zhang-upper-bound.md)
- [Smoothed lower bound for the shadow vertex simplex method](shadow-vertex-smoothed-lower-bound.md)

## Proof depends on

- [Huiberts-Lee-Zhang smoothed complexity O(sigma^{-3/2} d^{13/4} log^{7/4} n)](huiberts-lee-zhang-upper-bound.md)
- [Shadow vertices are bounded by edges of the polar section](shadow-vertices-and-polar-section.md)

## Sources

- E. Bach, S. Huiberts, "Optimal Smoothed Analysis of the Simplex Method", arXiv preprint (2025), arXiv:2504.04197.
- S. Huiberts, Y. T. Lee, X. Zhang, "Upper and Lower Bounds on the Smoothed Complexity of the Simplex Method", STOC (2023), TheoretiCS 4 (2025), arXiv:2211.11860.
