# Stable set polytopes with extension complexity 2^Omega(sqrt n)

For every $m \ge 2$ there is a graph $H_m$ on $m$ vertices whose stable set polytope satisfies $\mathrm{xc}(\mathrm{STAB}(H_m)) \ge (3/2)^{\lfloor \sqrt{m/2} \rfloor}$. The graph is obtained from a gadget on $2p^2$ vertices, with $p = \lfloor \sqrt{m/2} \rfloor$, whose maximum stable sets project linearly onto the vertices of $\mathrm{COR}(p)$, padded with isolated vertices.

## Proof sketch

The maximum-cardinality stable sets of the gadget form a face of $\mathrm{STAB}$ whose coordinate projection is $\mathrm{COR}(p)$; apply the face and projection lemma and the correlation bound.

## Depends on

- [The correlation polytope](correlation-polytope.md)
- [Stable set polytope](../../../GraphTheory/graph-invariants-and-labelings/theta-function-of-a-graph/stab.md)

## Proof depends on

- [Kaibel-Weltge: the correlation polytope has extension complexity at least (3/2)^n](correlation-polytope-lower-bound.md)
- [Faces and projections do not increase extension complexity](extension-complexity-faces-and-projections.md)

## Sources

- S. Fiorini, S. Massar, S. Pokutta, H. R. Tiwary and R. de Wolf, "Exponential Lower Bounds for Polytopes in Combinatorial Optimization", Journal of the ACM 62(2), 2015.
- V. Kaibel and S. Weltge, "A Short Proof that the Extension Complexity of the Correlation Polytope Grows Exponentially", Discrete & Computational Geometry 53(2), 2015.
