# Equations with abelian predicates are undecidable in hyperbolic groups with large abelianization

If $G$ is a hyperbolic group whose abelianization has torsion-free rank at least two, then no algorithm decides whether a system of equations over $G$ has a solution whose abelianization satisfies given equations.

Let $G$ be a word-hyperbolic group such that the torsion-free rank of $G^{\mathrm{ab}} = G / [G, G]$ (the rank of the free abelian group $G^{\mathrm{ab}}$ modulo torsion) is at least $2$. Then $\mathcal{DP}(G, \mathrm{ab})$ is undecidable (Theorem B, proved as Theorem 7.10, of the source).

When the abelianization of a hyperbolic group is finite the problem is decidable (source); the case of torsion-free rank one is left open there.

## Depends on

- [Diophantine problem with abelian predicates](diophantine-problem-with-abelian-predicates.md)
- [Word-hyperbolic groups](../../geometric-group-theory/hyperbolic-groups/is-hyperbolic.md)
- [Group](../../group-basics/group.md)
- [Commutator subgroup of a group](../../commutators-and-engel-conditions/commutator-subgroup.md)
- [Quotient group by a normal subgroup](../../group-basics/quotient-group.md)
- [Abelian group](../../group-basics/abelian-group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Abelianization of a group](../../commutators-and-engel-conditions/abelianization.md)
- [Solution set of a system of equations](../equationally-noetherian-groups/solutions-2.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

As for right-angled Artin groups, the proof applies the source's technical lemma (Lemma 5.3), which interprets integer arithmetic in $(G, \mathrm{ab})$ by positive existential formulas once two suitable elements with independent images in the abelianization are available, together with the definability of their exponent sums. In a hyperbolic group, centralizers of infinite-order elements are virtually cyclic, which supplies the required definitions (Lemma 7.4 and the following results).

## Sources

- L. Ciobanu and A. Garreta, "Group equations with abelian predicates", International Mathematics Research Notices 2024 (2024), no. 5, 4119–4159, https://doi.org/10.1093/imrn/rnad179; read in arXiv:2204.13946v1 (Theorem B in the introduction, Lemma 5.3, Lemma 7.4 and Theorem 7.10 of arXiv:2204.13946v1).
