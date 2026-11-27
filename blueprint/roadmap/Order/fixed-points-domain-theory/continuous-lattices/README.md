# Continuous lattices

Scott's continuous lattices are the complete lattices in which every element is approximated from below by the elements way below it (D. Scott, *Continuous Lattices*, Oxford PRG-7 (1971), §2). In a complete lattice with its Scott topology, $x$ is way below $y$, written $x \ll y$, when $y$ lies in the interior of the principal upper set of $x$. Continuity means $y = \bigsqcup \{x \mid x \ll y\}$ for every $y$ (Definition 2.3). Scott proves that the continuous lattices are exactly the injective $T_0$ spaces (Theorem 2.12). They are closed under products, retracts and continuous function spaces (Proposition 2.9, Proposition 2.10, Theorem 3.3), and under inverse limits along projections (Proposition 4.1). This last closure property is what makes his inverse-limit model $D_\infty \cong [D_\infty \to D_\infty]$ a continuous lattice. The pages below state Scott's definitions and the example of the two-element lattice.

- [Scott's way-below relation](way-below.md)
- [Continuous lattice](is-continuous-lattice.md)
- [The two-element lattice is continuous](is-continuous-lattice-bool.md)

## Related topics

- [Scott's graph model](../scott-s-graph-model/README.md): $P(\omega)$, an algebraic, hence continuous, lattice, and an injective space.
- [Scott's inverse-limit theorem](../scott-s-inverse-limit-theorem.md): continuous lattices solving $D \cong [D \to D]$.
- [Scott-continuous maps and least fixed points](../scott-continuous-maps-and-least-fixed-points/README.md): the continuous maps between complete lattices.
