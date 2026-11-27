# The Post correspondence problem with a rational constraint is undecidable for free groups

There is a rational subset $\mathcal{R}$ of a free group such that no algorithm decides, for homomorphisms $g, h$ between free groups, whether some non-trivial $x \in \mathcal{R}$ satisfies $g(x) = h(x)$.

For finite alphabets $\Sigma$ and $\Delta$, homomorphisms $g, h\colon F(\Sigma) \to F(\Delta)$ and a rational subset $\mathcal{R} \subseteq F(\Sigma)$ (the image of a regular language over $\Sigma^{\pm 1}$), the Post correspondence problem with rational constraint asks whether there is $x \in \mathcal{R}$ with $x \ne 1$ and $g(x) = h(x)$. There exists a rational constraint $\mathcal{R}$ such that this problem, with input $g$ and $h$, is undecidable (Theorem B of the source).

The source leaves open whether the unconstrained Post correspondence problem for free groups is decidable.

## Depends on

- [Rational subset membership problem](../submonoid-and-rational-subset-membership/rational-subset-membership-problem.md)
- [Group](../../../group-basics/group.md)
- [Multiplication-preserving maps and group homomorphisms](../../../semigroups-and-monoids/group-homomorphism.md)

## Proof depends on

- [The generalized Post correspondence problem is undecidable in every group containing a non-abelian free subgroup](gpcp-undecidable-groups-with-free-subgroups.md)

## Expansion

The source first shows that the generalized Post correspondence problem for free groups, with constants $u_1, u_2, v_1, v_2$ and the requirement $x \ne 1$, is undecidable when neither map is injective (Lemma 2, building on Myasnikov, Nikolaev and Ushakov). It then encodes the constants into letters at the two ends of $x$, reducing this problem to the extreme-letter restriction, which asks for $x = ayb$ with fixed extreme letters $a, b$ and $y$ in a free factor $F(\Omega)$; such sets of words are rational, so the constrained problem is undecidable.

## Sources

- L. Ciobanu and A. D. Logan, "Variations on the Post correspondence problem for free groups", Developments in Language Theory (DLT 2021), Lecture Notes in Computer Science 12811 (2021), 90–102, https://doi.org/10.1007/978-3-030-81508-0_8; read in arXiv:2104.05772v1 (Theorem B in the introduction, restated as Theorem 3 in Section 4, and Lemma 2 in Section 2, of arXiv:2104.05772v1; the llncs class numbers lemmas and theorems separately).
