# Thompson's group F has a subgroup with undecidable conjugacy problem and decidable membership

Thompson's group $F$ has a subgroup $H$, a closed subgroup in the sense of piecewise-$H$ functions, such that membership in $H$ is decidable while the conjugacy problem in $H$ is undecidable; $F$ itself has conjugacy problem decidable in linear time.

Thompson's group $F$ is the group of piecewise-linear homeomorphisms of $[0, 1]$ with finitely many breakpoints, all in $\mathbb{Z}[1/2]$, and all slopes integer powers of $2$; its elements are given as words in a finite generating set of $F$. There is a subgroup $H \le F$ such that (Theorem 1.1 of the source):

1. the membership problem in $H$ is decidable: some algorithm decides, for an element of $F$, whether it lies in $H$;
2. the conjugacy problem in $H$ is undecidable: no algorithm decides, for two elements of $H$, whether they are conjugate by an element of $H$.

The subgroup $H$ is closed: every element of $F$ that, on each of finitely many pieces with dyadic endpoints, coincides with a restriction of an element of $H$ lies in $H$ (Definitions 1.2 and 1.3). The source realizes $H$ as a diagram group of a finite tree rewriting system; such diagram groups need not be finitely generated.

## Depends on

- [Thompson's group $F$ by its standard presentation](thompson-f.md)
- [Group](../../../group-basics/group.md)
- [Membership problem for a subset of a finitely generated group](../../../presentations-and-decision-problems/membership-and-equation-problems/submonoid-and-rational-subset-membership/membership-problem-for-a-subset.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Solvable conjugacy problem for a quotient of a free group](../../../presentations-and-decision-problems/decision-problems-in-free-abelianized-extensions/conjugacy-problem-solvable.md)
- [Homeomorphism](../../../../Topology/topological-spaces/homeomorphism.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](../../../presentations-and-decision-problems/word-problem-for-groups/novikov-unsolvable.md)

## Expansion

Closed subgroups of $F$ are the diagram groups $DG(\mathcal{P}, a)$ of tree rewriting systems $\mathcal{P}$, embedded in $F$ (Definition 2.7 in the version read). There is a finite tree rewriting system defining a semigroup that is a group with undecidable word problem (Lemma 3.1); the corresponding diagram group has undecidable conjugacy problem, since conjugacy of certain spherical diagrams encodes equality of words in that group, while membership in the diagram group of a finite tree rewriting system, viewed inside $F$, is decidable by a procedure that uses the finite rewriting system to test whether a reduced diagram belongs to the group (Theorem 2.13); closedness alone does not give it.

## Sources

- G. Golan-Polak and M. Sapir, "On closed subgroups of the R. Thompson group F", Israel Journal of Mathematics 267 (2025), no. 1, 35–84, https://doi.org/10.1007/s11856-024-2692-z; read in arXiv:2105.00531v1 (Theorem 1.1, Definitions 1.2, 1.3 and 2.7, Theorem 2.13 and Lemma 3.1 of arXiv:2105.00531v1).
