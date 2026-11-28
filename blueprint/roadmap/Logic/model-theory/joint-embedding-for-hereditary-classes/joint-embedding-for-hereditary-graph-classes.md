# Joint embedding for hereditary graph classes is undecidable

There is no algorithm that decides, given finitely many forbidden induced subgraphs, whether the class of finite graphs avoiding them has the joint embedding property, that is, whether that hereditary class is atomic.

**Theorem (Braunfeld).** There is no algorithm that, given a finite set $\mathcal F$ of finite graphs, decides whether the hereditary graph class $\mathrm{Forb}(\mathcal F)$ of finite graphs with no induced subgraph isomorphic to a member of $\mathcal F$ has the [joint embedding property](joint-embedding-property.md). This is Theorem 1.2 of arXiv:1903.11932v4, proved by a reduction from the tiling problem.

Graphs here are finite simple graphs, so $\mathrm{Forb}(\mathcal F)$ is given by finitely many forbidden induced subgraphs. The complementary problem, failure of the JEP, is recursively enumerable, so the JEP problem is co-recursively enumerable and undecidable.

## Depends on

- [Joint embedding property](joint-embedding-property.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Co-recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces the tiling problem for the quadrant $\mathbb N^2$ (Berger), given by finitely many tile types and forbidden horizontal and vertical adjacencies. It is first carried out for graphs with finitely many unary predicates (colors). One builds a colored graph $A^*$ representing a grid and a colored graph $B^*$ representing a supply of tiles, and chooses finitely many forbidden configurations such that a joint embedding of $A^*$ and $B^*$ encodes a tiling; conversely, if the tiling problem has a solution, the class admits a joint embedding procedure for all pairs. Thus the class $\mathcal G_{\mathcal T}$ built from a tiling problem $\mathcal T$ has the JEP iff $\mathcal T$ has a solution (Proposition 3.2). The colors are then removed: each color is replaced by attaching a member of an infinite antichain of $2$-connected graphs with base points, which yields a reduction to hereditary classes of plain graphs preserving the JEP (Section 4).

## Sources

- S. Braunfeld, "The undecidability of joint embedding and joint homomorphism for hereditary graph classes", *Discrete Mathematics & Theoretical Computer Science* 21(2), Permutation Patterns 2018, 2019, paper 9, <https://doi.org/10.23638/DMTCS-21-2-9>; numbers from arXiv:1903.11932v4, <https://arxiv.org/abs/1903.11932v4>: Theorem 1.2 (proved as Theorem 4.17), Proposition 3.2 and Section 4 (Definitions 4.1 to 4.12, Lemmas 4.5 to 4.14).
- S. W. Braunfeld, *Infinite Limits of Finite-Dimensional Permutation Structures, and their Automorphism Groups: Between Model Theory and Combinatorics*, PhD dissertation, Rutgers, The State University of New Jersey, 2018; read as arXiv:1805.04219v1, <https://arxiv.org/abs/1805.04219v1>: Theorem 9.1.2, Proposition 9.4.1 and Theorem 9.5.15 of that version (the same result).
