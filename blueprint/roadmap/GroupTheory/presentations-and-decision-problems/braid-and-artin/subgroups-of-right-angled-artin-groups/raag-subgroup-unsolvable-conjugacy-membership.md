# Some right-angled Artin group has a finitely presented subgroup with unsolvable conjugacy and membership problems

There are a right-angled Artin group $A$ and a finitely presented subgroup $H$ of $A$ such that the conjugacy problem of $H$ and the membership problem of $H$ in $A$ are both unsolvable.

There exist a right-angled Artin group $A$ and a finitely presented subgroup $H < A$ such that (Theorem 1.2 of the source):

1. the conjugacy problem of $H$ is unsolvable;
2. the membership problem for $H$ in $A$ is unsolvable: no algorithm decides, given a word in the generators of $A$, whether the element it represents lies in $H$.

The statement concerns a finitely presented subgroup; for finitely generated subgroups the corresponding results are much easier.

## Depends on

- [Membership problem for a subset of a finitely generated group](../../membership-and-equation-problems/submonoid-and-rational-subset-membership/membership-problem-for-a-subset.md)
- [Group](../../../group-basics/group.md)
- [Artin group](../artin-groups/artin-group.md)
- [Solvable conjugacy problem for a quotient of a free group](../../decision-problems-in-free-abelianized-extensions/conjugacy-problem-solvable.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](../../word-problem-for-groups/novikov-unsolvable.md)

## Expansion

For an exact sequence $1 \to N \to \Gamma \to Q \to 1$ with $\Gamma$ finitely generated, the fibre product $P = \{(\gamma_1, \gamma_2) : \gamma_1 N = \gamma_2 N\} < \Gamma \times \Gamma$ has unsolvable membership problem when $Q$ has unsolvable word problem (Lemma 3.3). Take $Q$ of type $F_3$ with unsolvable word problem and an aspherical presentation (Collins and Miller), and a Rips-type sequence with $N$ finitely generated and $\Gamma$ torsion-free hyperbolic and virtually special. A finite-index subgroup $\Gamma_0$ embeds in a right-angled Artin group $R$; the 1-2-3 theorem makes the fibre product $P_0 < \Gamma_0 \times \Gamma_0 \le R \times R = A$ finitely presented, with unsolvable membership problem (Theorem 3.4). Since centralizers of non-trivial elements of $\Gamma$ are cyclic and $Q$ is torsion-free, the centralizer of $(a, a)$, for $1 \ne a \in N$, lies in $P_0$, and a lemma of Baumslag, Bridson, Miller and Short (Lemma 3.6) turns unsolvable membership into unsolvable conjugacy for $P_0$ (Theorem 3.7). The subgroup $H$ of the theorem is $P_0$.

## Sources

- M. R. Bridson, "On the subgroups of right-angled Artin groups and mapping class groups", Mathematical Research Letters 20 (2013), no. 2, 203–212, https://doi.org/10.4310/MRL.2013.v20.n2.a1; read in arXiv:1205.5416v1 (Theorem 1.2, Lemma 3.3, Theorem 3.4, Lemma 3.6 and Theorem 3.7 of arXiv:1205.5416v1).
