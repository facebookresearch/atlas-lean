# Unary expansions of planar betweenness structures have Σ⁰₁-hard theories

If a set T of points of a Euclidean space contains a piece of a two-dimensional flat in a suitably dense way, then the first-order theory of all expansions of (T, β) by one unary predicate is Σ⁰₁-hard, hence undecidable.

**Theorem (Kuusisto, Meyers and Virtema).** Let $T \subseteq \mathbb R^n$ and let $\beta$ be the corresponding betweenness relation. If $T$ [extends linearly in 2D](affine-betweenness-structures.md), then the first-order theory of the unary expansion class $\mathcal E(T, \beta)$ is $\Sigma^0_1$-hard.

This applies for instance to $(\mathbb R^2, \beta)$, $(\mathbb Q^2, \beta)$, the plane of algebraic reals and $([0, 1]^3, \beta)$. Extending linearly in 1D does not suffice: the monadic $\Pi^1_1$-theory of $(\mathbb R, \beta)$ is decidable.

## Depends on

- [Affine betweenness structures](affine-betweenness-structures.md)
- [The arithmetical class $\Sigma_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces the complement of the tiling problem for the quadrant grid, which is $\Sigma^0_1$-complete because the tiling problem is $\Pi^0_1$-complete (Berger). Using the unary predicate together with constants $p_0, p_x, p_y$, first-order sentences define labeled *Cartesian frames* inside $(T, \beta)$, configurations built from discretely spaced sequences of points along lines, in which grid points are intersections of lines (Lemma 4.12). Since $T$ extends linearly in 2D, there is a uniform interpretation of a class of labeled *supergrids*, structures containing the grid, in these frames (Lemma 4.13). For a tile set $S$ the sentence $\psi_S = \varphi^S_{Cf} \wedge I(\varphi_S)$ has a model expanding $(T, \beta)$ iff the grid is $S$-tilable, so $S$ admits no tiling iff $\neg\psi_S$ belongs to the theory. The linked tiling page states only that the tiling problem is undecidable; $\Sigma^0_1$-hardness needs that it is $\Pi^0_1$-complete (Theorem 2.2 of the source, after Berger), and a complete expansion links a page for that and for the interpretation lemmas 4.12 and 4.13.

## Sources

- A. Kuusisto, J. Meyers and J. Virtema, "Undecidable First-Order Theories of Affine Geometries", *Logical Methods in Computer Science* 9(4), 2013, paper 26, pp. 1–23, <https://doi.org/10.2168/LMCS-9(4:26)2013>; numbers from arXiv:1310.8200v3, <https://arxiv.org/abs/1310.8200v3>: Section 2.4 (tiling problems, Theorem 2.2), Section 4: Lemmas 4.12 and 4.13, Theorem 4.15 and the remark following it.
