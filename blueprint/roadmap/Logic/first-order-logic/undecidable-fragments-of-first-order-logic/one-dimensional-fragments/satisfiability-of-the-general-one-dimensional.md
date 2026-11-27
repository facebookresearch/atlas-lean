# Satisfiability of the general one-dimensional fragment is undecidable

Dropping the uniformity condition from the one-dimensional fragment of first-order logic makes satisfiability undecidable: the general one-dimensional fragment $\mathrm{GF}_1$ has an undecidable satisfiability problem, in fact a $\Pi^0_1$-complete one.

**Theorem (Hella and Kuusisto).** The satisfiability problem for the [general one-dimensional fragment](general-one-dimensional-fragment.md) $\mathrm{GF}_1$, whether a given $\mathrm{GF}_1$ sentence over a finite relational vocabulary has a model, is undecidable. It is $\Pi^0_1$-complete: it lies in $\Pi^0_1$ because $\mathrm{GF}_1$ is a fragment of first-order logic, whose unsatisfiable sentences are recursively enumerable, and it is $\Pi^0_1$-hard.

The uniform one-dimensional fragment $\mathrm{UF}_1$, which differs only by the uniformity condition, has a decidable satisfiability problem. The source shows likewise that lifting the other restriction, one-dimensionality, by passing to the strongly uniform two-dimensional fragment $\mathrm{SUF}_2$ gives a $\Pi^0_1$-complete problem.

## Depends on

- [General one-dimensional fragment of first-order logic](general-one-dimensional-fragment.md)
- [The arithmetical class $\Pi_n$](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)

## Proof depends on

- [The tiling problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The hardness proof reduces the $\mathbb{N} \times \mathbb{N}$ tiling problem, which is $\Pi^0_1$-complete. Binary relations $H$ and $V$ represent the horizontal and vertical neighbors; because $\mathrm{GF}_1$ allows a quantified block such as $\exists y \exists z$ with a matrix mixing atoms $H(x, y)$, $V(x, z)$ and atoms on other variable sets, a sentence can demand that every element has an $H$-neighbor and a $V$-neighbor and that the grid closes (the $V$-neighbor of the $H$-neighbor is an $H$-neighbor of the $V$-neighbor), and that unary predicates for the tiles match along $H$ and $V$. Such a sentence is satisfiable iff the tile set tiles the grid.

## Sources

- L. Hella and A. Kuusisto, "One-dimensional fragment of first-order logic", in *Advances in Modal Logic 10 (AiML 2014)*, College Publications, 2014, pp. 274–293; read as arXiv:1404.4004v1, <https://arxiv.org/abs/1404.4004v1>: Section 5 (undecidable extensions) and Proposition C.1 of arXiv:1404.4004v1 ($\Pi^0_1$-completeness of $\mathrm{GF}_1$), with Theorem C.3 for $\mathrm{SUF}_2$; the abstract of the proceedings version states that the non-uniform one-dimensional and two-dimensional fragments are undecidable.
