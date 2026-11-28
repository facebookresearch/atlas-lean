# Betweenness with a finite unary predicate has a Π⁰₁-hard theory

If T extends linearly in 2D, the first-order theory of the structures (T, β, P) with P a finite subset of T is Π⁰₁-hard, hence undecidable.

**Theorem (Kuusisto, Meyers and Virtema).** Let $T \subseteq \mathbb R^n$ and let $\beta$ be the corresponding betweenness relation. If $T$ [extends linearly in 2D](affine-betweenness-structures.md), then the first-order theory of the class $\mathcal F(T, \beta) = \{(T, \beta, P) \mid P \subseteq T \text{ finite}\}$ is $\Pi^0_1$-hard.

The source notes that the argument adapts to other restricted expansion classes, with $P$ ranging over polygons, finite unions of closed rectangles or semialgebraic sets.

## Depends on

- [Affine betweenness structures](affine-betweenness-structures.md)
- [The arithmetical class $\Pi_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces the complement of the periodic tiling problem, which is $\Sigma^0_1$-complete (Gurevich and Koryakov): does a tile set tile some torus, a finite grid whose east border wraps to the west and north border to the south? Finite labeled Cartesian frames are defined in $(T, \beta, P)$ with $P$ finite (Lemma 5.5), labeled tori are interpreted uniformly in them (Lemma 5.6), and a sentence has a model in $\mathcal F(T, \beta)$ iff some torus is tilable; its negation lies in the theory iff no torus is tilable.

## Sources

- A. Kuusisto, J. Meyers and J. Virtema, "Undecidable First-Order Theories of Affine Geometries", *Logical Methods in Computer Science* 9(4), 2013, paper 26, pp. 1–23, <https://doi.org/10.2168/LMCS-9(4:26)2013>; numbers from arXiv:1310.8200v3, <https://arxiv.org/abs/1310.8200v3>: Section 5: Lemmas 5.5 and 5.6, Theorem 5.7; Theorem 2.4 (periodic tiling).
- Y. Gurevich and I. O. Koryakov, "Remarks on Berger's paper on the domino problem", *Siberian Mathematical Journal* 13(2):319–321, 1972, <https://doi.org/10.1007/BF00971620>: the periodic tiling problem, as recalled in Section 2.2 of the version of the first source read.
