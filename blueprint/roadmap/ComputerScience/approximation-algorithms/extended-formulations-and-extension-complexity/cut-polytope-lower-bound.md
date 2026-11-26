# The cut polytope has exponential extension complexity

The **cut polytope** $\mathrm{CUT}(n)$ is the convex hull of the edge characteristic vectors of all cuts $\delta(X)$ of the complete graph on $n$ vertices. The covariance map of De Simone is an invertible linear map carrying $\mathrm{COR}(n-1)$ onto $\mathrm{CUT}(n)$, so $\mathrm{xc}(\mathrm{CUT}(n)) = \mathrm{xc}(\mathrm{COR}(n-1))$, and therefore $\mathrm{xc}(\mathrm{CUT}(n)) \ge (3/2)^{n-1}$ for $n \ge 2$.

## Proof sketch

Send $bb^\top$ to the cut indicator of $X = \{i : b_i = 1\}$ in $K_{n}$ with an extra vertex: $x_{\{i, n\}} = b_i$ and $x_{\{i,j\}} = b_i + b_j - 2b_ib_j$; this map is linear and invertible on the affine hulls. Invertible linear maps preserve extension complexity.

## Depends on

- [The correlation polytope](correlation-polytope.md)

## Proof depends on

- [Kaibel-Weltge: the correlation polytope has extension complexity at least (3/2)^n](correlation-polytope-lower-bound.md)
- [Faces and projections do not increase extension complexity](extension-complexity-faces-and-projections.md)

## Sources

- C. De Simone, "The Cut Polytope and the Boolean Quadric Polytope", Discrete Mathematics 79(1), 1990.
- S. Fiorini, S. Massar, S. Pokutta, H. R. Tiwary and R. de Wolf, "Exponential Lower Bounds for Polytopes in Combinatorial Optimization", Journal of the ACM 62(2), 2015.
- V. Kaibel and S. Weltge, "A Short Proof that the Extension Complexity of the Correlation Polytope Grows Exponentially", Discrete & Computational Geometry 53(2), 2015.
