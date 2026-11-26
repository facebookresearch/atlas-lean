# Huiberts-Lee-Zhang smoothed complexity O(sigma^{-3/2} d^{13/4} log^{7/4} n)

There is a simplex method whose smoothed complexity on linear programs with $d$ variables and $n$ constraints is

$$
O\!\left(\sigma^{-3/2} d^{13/4} \log^{7/4} n\right)
$$

pivot steps, improving the dependence on the noise level from $\sigma^{-2}$ to $\sigma^{-3/2}$. The same analysis yields a nearly tight upper bound on the expected number of vertices of smoothed polygons in the plane.

## Proof sketch

The proof gives a new analysis of the shadow bound, again counting edges of the polar section, but bounding the expected number of short edges through a finer account of how Gaussian noise distributes edge lengths along the section boundary instead of a uniform per-edge length bound. The improved shadow bound is converted into a pivot bound by the two-phase reduction used for the Dadush-Huiberts bound.

## Depends on

- [Dadush-Huiberts shadow bound for smoothed unit linear programs](dadush-huiberts-shadow-bound.md)

## Proof depends on

- [Dadush-Huiberts shadow bound for smoothed unit linear programs](dadush-huiberts-shadow-bound.md)
- [Shadow vertices are bounded by edges of the polar section](shadow-vertices-and-polar-section.md)

## Sources

- S. Huiberts, Y. T. Lee, X. Zhang, "Upper and Lower Bounds on the Smoothed Complexity of the Simplex Method", STOC (2023), TheoretiCS 4 (2025), arXiv:2211.11860.
