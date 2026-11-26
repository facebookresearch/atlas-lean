# Smoothed lower bound for the shadow vertex simplex method

For every $d$ and $\sigma$ there are base programs such that, after Gaussian smoothing with standard deviation $\sigma$, the shadow vertex simplex method requires at least

$$
\Omega\!\left(\min\left(\sigma^{-1/2} d^{-1/2} \log^{-1/4} d,\; 2^d\right)\right)
$$

pivot steps with high probability. This is the first nontrivial lower bound on the smoothed complexity of the simplex method.

## Proof sketch

The instances come from a variation of the extended formulation of the regular $2^k$-gon: a polyhedron in dimension $O(k)$ with $O(k)$ constraints whose projection onto a fixed plane is close to a regular polygon with $2^k$ vertices. Choosing $k$ so that the angular spacing of the polygon vertices exceeds the distortion caused by the perturbation, most polygon vertices survive in the shadow of the smoothed polyhedron, and the shadow vertex path must visit each of them.

## Depends on

- [Gaussian-smoothed linear programs and smoothed pivot complexity](gaussian-smoothed-linear-programs.md)
- [The shadow vertex pivot rule and the smoothed shadow bound](shadow-vertex-rule-and-shadow-bound.md)

## Proof depends on

- [Shadow vertices are bounded by edges of the polar section](shadow-vertices-and-polar-section.md)

## Sources

- S. Huiberts, Y. T. Lee, X. Zhang, "Upper and Lower Bounds on the Smoothed Complexity of the Simplex Method", STOC (2023), TheoretiCS 4 (2025), arXiv:2211.11860.
