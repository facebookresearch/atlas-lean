# Scott's inverse-limit theorem

The domain equation $D \cong [D \to D]$ has non-trivial solutions among continuous lattices. For every continuous lattice $D_0$ there is a continuous lattice $D$ such that
- $D$ is order-isomorphic to the lattice $[D \to D]$ of its Scott-continuous self-maps, ordered pointwise, and
- $D_0$ is a projection of $D$: there are Scott-continuous maps $e : D_0 \to D$ and $p : D \to D_0$ with $p \circ e = \mathrm{id}$ and $e \circ p \le \mathrm{id}$.

If $D_0$ has two distinct elements, so has $D$, because $e$ is injective; the [two-element lattice](continuous-lattices/is-continuous-lattice-bool.md) satisfies the hypothesis.

**Source.** D. Scott, *Continuous Lattices*, Oxford PRG-7 (1971), §4: Proposition 4.1, Proposition 4.2 and Theorem 4.4. Continuous lattices are as in Definition 2.3, stated here with Scott's own [way-below relation](continuous-lattices/way-below.md), and projections are as in Definition 3.6. Scott starts from a continuous lattice $D_0$ and a chosen projection pair $D_0 \rightleftarrows D_1 = [D_0 \to D_0]$. He sets $D_{n+1} = [D_n \to D_n]$, lifts the pair to each level (Proposition 3.7), and takes $D_\infty$ to be the inverse limit along the projections. Then:
- $D_\infty$ is a continuous lattice (Proposition 4.1);
- each $D_n$ is a projection of $D_\infty$ (Proposition 4.2);
- $D_\infty$ is homeomorphic to $[D_\infty \to D_\infty]$ (Theorem 4.4).

Scott also remarks that for $D_0 = \{\bot, \top\}$ the two possible initial projections give non-isomorphic limits.

**How the statement relates to Scott's theorem.** The hypotheses are exactly Scott's: $D_0$ is a continuous lattice. The conclusion is weaker in one respect: it asserts that some $D$ exists, while Scott constructs a specific one, $D_\infty$, from the chosen projection pair. The conclusion uses an order isomorphism where Scott states a homeomorphism; for continuous lattices the two carry the same information. A homeomorphism preserves the specialisation order. Conversely, an order isomorphism between complete lattices is a homeomorphism for their Scott topologies, and for continuous lattices Scott shows that the topology of $[D \to D]$ is its Scott topology (Theorem 3.3).

With application and abstraction transported along the isomorphism, $D_\infty$ is a model of the untyped λ-calculus in which both β and η hold, unlike the graph model.

## Background

- [Continuous lattice](continuous-lattices/is-continuous-lattice.md): the class of lattices in the statement.
- [Arbitrary pointwise suprema of Scott-continuous maps between complete lattices](scott-continuous-maps-and-least-fixed-points/scott-continuous-s-sup.md): $[D \to D]$ is again a complete lattice, so the iteration $D_{n+1} = [D_n \to D_n]$ stays among complete lattices.
- [Scott's graph model](scott-s-graph-model/README.md): a simpler model, where $[P(\omega) \to P(\omega)]$ is only a retract of $P(\omega)$ and η fails.
- [Models of the untyped lambda calculus](../../ComputerScience/programming-language-semantics/models-of-the-untyped-lambda-calculus/README.md): the λ-calculus side.

## Sources

- D. Scott, *Continuous Lattices*, Technical Monograph PRG-7, Oxford University Computing Laboratory, August 1971, <http://www.cs.ox.ac.uk/files/3229/PRG07.pdf>. This is the pre-publication monograph version of the paper in *Toposes, Algebraic Geometry and Logic*, Lecture Notes in Mathematics 274 (1972), 97–136; theorem numbers here are those of PRG-7.
