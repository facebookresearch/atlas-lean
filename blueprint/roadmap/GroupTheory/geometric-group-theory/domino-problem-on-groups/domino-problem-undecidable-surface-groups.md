# The domino problem is undecidable on surface groups

For every $g \ge 1$, the fundamental group of the closed orientable surface of genus $g$ has undecidable domino problem.

For $g \ge 1$ let

$$
G_g = \langle a_1, b_1, \dots, a_g, b_g \mid [a_1, b_1] \cdots [a_g, b_g] \rangle, \qquad [a, b] = aba^{-1}b^{-1},
$$

the fundamental group of the closed orientable surface of genus $g$. The domino problem of $G_2$ is undecidable (Theorem 17 of the source), and hence the domino problem of $G_g$ is undecidable for every $g \ge 1$ (Corollary 18).

## Depends on

- [Domino problem of a finitely generated group](domino-problem-of-a-group.md)
- [Group](../../group-basics/group.md)
- [Surface groups](../../presentations-and-decision-problems/free-subgroups-of-one-relator-groups/is-surface-group.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

For $g = 1$, $G_1 \cong \mathbb{Z}^2$ and the domino problem is the Wang tiling problem, undecidable by Berger. For $g \ge 2$ all the groups $G_g$ are commensurable, and decidability of the domino problem is a commensurability invariant, so the case $g = 2$ suffices. The source proves that the domino problem is undecidable on every orbit graph of a non-deterministic substitution with an expanding eigenvalue (Theorem 7), extending Kari's theorem for the hyperbolic plane, and then finds such an orbit graph inside the Cayley graph of $G_2$, with labels that are computable locally, giving a reduction to the domino problem of $G_2$. The source also notes that if every one-ended hyperbolic group contains a surface group (Gromov's question), then a hyperbolic group has decidable domino problem exactly when it is virtually free.

## Sources

- N. Aubrun, S. Barbieri and E. Moutot, "The domino problem is undecidable on surface groups", 44th International Symposium on Mathematical Foundations of Computer Science (MFCS 2019), Leibniz International Proceedings in Informatics (LIPIcs) 138 (2019), article 46, https://doi.org/10.4230/LIPIcs.MFCS.2019.46; arXiv:1811.08420v1 (Theorem 7, Theorem 17 and Corollary 18 of arXiv:1811.08420v1).
