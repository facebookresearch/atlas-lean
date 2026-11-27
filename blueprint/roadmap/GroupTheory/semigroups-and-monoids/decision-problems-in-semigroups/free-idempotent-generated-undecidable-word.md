# A free idempotent generated semigroup over a finite band with undecidable word problem

There is a finite band $S$ with biordered set $\mathcal{E}$ such that every maximal subgroup of the free idempotent generated semigroup $\mathrm{IG}(\mathcal{E})$ has decidable word problem while $\mathrm{IG}(\mathcal{E})$ itself has undecidable word problem.

A band is a semigroup in which every element is idempotent. For a semigroup $S$ with set of idempotents $E$ (with its biordered set structure $\mathcal{E}$), the free idempotent generated semigroup over $\mathcal{E}$ is

$$
\mathrm{IG}(\mathcal{E}) = \mathrm{Sgp}\langle E \mid e \cdot f = ef \ \text{for all } e, f \in E \text{ with } \{e, f\} \cap \{ef, fe\} \ne \emptyset \rangle ,
$$

where $ef$ is the product in $S$ and $e \cdot f$ the product of generators. There is a finite band $S$ such that, for $\mathcal{E} = \mathcal{E}(S)$, all maximal subgroups of $\mathrm{IG}(\mathcal{E})$ have decidable word problem but the word problem of $\mathrm{IG}(\mathcal{E})$ with respect to the finite generating set $E$ is undecidable (Theorem 5.5 of the source).

More precisely (Theorem 5.3), if $G$ is a finitely presented group with decidable word problem and $H$ a finitely generated subgroup of $G$ with undecidable membership problem, the source builds a finite band $B_{G,H}$ such that every non-trivial maximal subgroup of $\mathrm{IG}(\mathcal{B}_{G,H})$ is isomorphic to $G$ and $\mathrm{IG}(\mathcal{B}_{G,H})$ has undecidable word problem. On the positive side, for finite $\mathcal{E}$ it is decidable whether a word represents a regular element, and the word problem restricted to regular words is decidable when all maximal subgroups have decidable word problem.

## Depends on

- [Solvable word problem](../../presentations-and-decision-problems/word-problem-for-groups/word-problem-solvable.md)
- [Group](../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Membership problem for a subset of a finitely generated group](../../presentations-and-decision-problems/membership-and-equation-problems/submonoid-and-rational-subset-membership/membership-problem-for-a-subset.md)

## Expansion

Theorem 5.2 shows that a solution of the word problem of $\mathrm{IG}(\mathcal{B}_{G,H})$ would decide membership in $H$ within $G$; the band $B_{G,H}$ has five $\mathcal{D}$-classes, the least being a zero. Mihailova's theorem (Theorem 5.4 of the source) supplies the pair: for a free group $\Gamma$ of rank at least 2, the group $G = \Gamma \times \Gamma$ has decidable word problem and a finitely generated subgroup with undecidable membership problem, namely the fibre product of a surjection from $\Gamma$ onto a finitely presented group with undecidable word problem. Since every non-trivial maximal subgroup is isomorphic to $\Gamma \times \Gamma$, all maximal subgroups have decidable word problem.

## Sources

- I. Dolinka, R. D. Gray and N. Ruškuc, "On regularity and the word problem for free idempotent generated semigroups", Proceedings of the London Mathematical Society 114 (2017), no. 3, 401–432, https://doi.org/10.1112/plms.12011; arXiv:1412.5167v4 (Theorems 5.2, 5.3, 5.4 (Mihailova) and 5.5 of arXiv:1412.5167v4).
