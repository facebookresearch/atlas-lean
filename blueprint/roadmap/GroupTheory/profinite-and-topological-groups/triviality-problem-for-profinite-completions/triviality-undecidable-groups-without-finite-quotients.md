# Triviality is undecidable for super-perfect groups with compact classifying space and no finite quotients

No algorithm decides, given a finite presentation of a super-perfect group that has a compact classifying space and no proper subgroups of finite index, whether the group is trivial.

Let $\mathcal{J}$ be the class of super-perfect groups ($H_1(G; \mathbb{Z}) = H_2(G; \mathbb{Z}) = 0$) that have a compact classifying space and no proper subgroups of finite index. There does not exist an algorithm that, given a finite presentation of a group $\Gamma$ and a guarantee that $\Gamma \in \mathcal{J}$, can determine whether or not $\Gamma \cong \{1\}$ (Theorem D of the source).

More precisely (Theorem 3.1), there are a finite set $X$ and a recursive sequence $(R_n)$ of finite sets of words of fixed cardinality such that the groups $Q_n = \langle X \mid R_n \rangle$ all lie in $\mathcal{J}$, no algorithm determines which $Q_n$ are trivial, and each non-trivial $Q_n$ has unsolvable word problem.

## Depends on

- [Group](../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](../../presentations-and-decision-problems/word-problem-for-groups/novikov-unsolvable.md)

## Expansion

The proof starts from the Collins–Miller theorem: a recursive sequence of torsion-free groups with aspherical presentations of fixed size whose triviality is undecidable (Theorem 3.2 of the source). An algorithm the author attributes to C. F. Miller III turns a finite presentation of a perfect group into one of a super-perfect group with no finite quotients that is trivial exactly when the original is, keeping asphericity, so a compact classifying space survives.

## Sources

- M. R. Bridson, "Decision problems and profinite completions of groups", Journal of Algebra 326 (2011), no. 1, 59–73, https://doi.org/10.1016/j.jalgebra.2010.06.019; read in arXiv:0810.0390v1 (Theorem D of the introduction and Theorems 3.1 and 3.2 of arXiv:0810.0390v1).
