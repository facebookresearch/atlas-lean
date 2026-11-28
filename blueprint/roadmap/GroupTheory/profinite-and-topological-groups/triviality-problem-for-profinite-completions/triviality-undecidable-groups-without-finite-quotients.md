# Triviality is undecidable for super-perfect groups with compact classifying space and no finite quotients

No algorithm decides, given a finite presentation of a super-perfect group that has a compact classifying space and no proper subgroups of finite index, whether the group is trivial.

Let $\mathcal{J}$ be the class of super-perfect groups ($H_1(G; \mathbb{Z}) = H_2(G; \mathbb{Z}) = 0$) that have a compact classifying space and no proper subgroups of finite index. There does not exist an algorithm that, given a finite presentation of a group $\Gamma$ and a guarantee that $\Gamma \in \mathcal{J}$, can determine whether or not $\Gamma \cong \{1\}$ (Theorem D of the source).

More precisely (Theorem 3.1), there are a finite set $X$ and a recursive sequence $(R_n)$ of finite sets of words of fixed cardinality such that the groups $Q_n = \langle X \mid R_n \rangle$ all lie in $\mathcal{J}$, no algorithm determines which $Q_n$ are trivial, and each non-trivial $Q_n$ has unsolvable word problem.

## Depends on

- [Group](../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Eilenberg–MacLane space](../../../Topology/algebraic-topology/is-eilenberg-maclane-space.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](../../presentations-and-decision-problems/word-problem-for-groups/novikov-unsolvable.md)

## Expansion

The proof starts from the Collins–Miller theorem: a recursive sequence of finite presentations $\Pi_n$, with fixed numbers of generators and relators, of torsion-free groups $\Lambda_n$ whose triviality is undecidable, where $\Pi_n$ is aspherical whenever $\Lambda_n$ is non-trivial (Theorem 3.2 of the source); the trivial groups of the sequence get no such promise. Amalgamating a copy of a finitely presented group with no finite quotients, such as Higman's group, along each generator gives presentations of groups $\Lambda'_n$ with no non-trivial finite quotients, trivial exactly when $\Lambda_n$ is, and aspherical when non-trivial (Definition 3.3 and Lemma 3.4); this is the step that excludes finite quotients. An algorithm the author learnt from C. F. Miller III outputs a finite presentation of the universal central extension of a finitely presented perfect group (Proposition 3.5 and Corollary 3.6). Applied to the groups $\Lambda'_n$, it gives super-perfect groups $Q_n$; passing to the universal central extension preserves having no non-trivial finite quotients and, from a $2$-dimensional classifying space, gives a compact classifying space (Proposition 1.3(4), (5) and (8)), and these are the properties the theorem states for the non-trivial $Q_n$. A good expansion adds and links pages for the Collins–Miller theorem and for Proposition 1.3 of the source.

## Sources

- M. R. Bridson, "Decision problems and profinite completions of groups", Journal of Algebra 326 (2011), no. 1, 59–73, https://doi.org/10.1016/j.jalgebra.2010.06.019; read in arXiv:0810.0390v1 (Theorem D of the introduction, Proposition 1.3, Theorems 3.1 and 3.2, Definition 3.3, Lemma 3.4, Proposition 3.5 and Corollary 3.6 of arXiv:0810.0390v1).
