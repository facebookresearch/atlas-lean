# Decidability of submonoid membership does not pass to finite extensions

There are a group $G$ and a finite-index subgroup $\widetilde G \le G$ such that submonoid membership is decidable in $\widetilde G$ but undecidable in $G$.

There exist a group $G$ and a finite-index subgroup $\widetilde G \le G$ such that the submonoid membership problem is decidable in $\widetilde G$ and undecidable in $G$ (Corollary 3.2 of the source). Concretely $G = L \times H$ and $\widetilde G = L \times \mathbb{Z}^d$, where $L = (\mathbb{Z}/2\mathbb{Z}) \wr \mathbb{Z}^2$ is the two-dimensional lamplighter group, $H$ is a finitely generated virtually abelian group from Shafrir's construction, and $\mathbb{Z}^d$ is a finite-index subgroup of $H$.

The source proves (Theorem 3.1) that, for a prime $p$, submonoid membership is decidable in every group $\mathcal{Y} \rtimes \mathbb{Z}^n$ with $\mathcal{Y}$ a finitely presented module over $\mathbb{F}_p[X_1^{\pm}, \dots, X_n^{\pm}]$, the $i$-th generator of $\mathbb{Z}^n$ acting on $\mathcal{Y}$ as multiplication by $X_i$; this includes the lamplighter groups $(\mathbb{Z}/p\mathbb{Z}) \wr \mathbb{Z}^n$ (take $\mathcal{Y} = \mathbb{F}_p[X_1^{\pm}, \dots, X_n^{\pm}]$), which gives decidability in $\widetilde G$.

## Depends on

- [Submonoid membership problem](submonoid-membership-problem.md)
- [Group](../../../group-basics/group.md)
- [Restricted wreath product](../../../soluble-finite-groups/solubility-nilpotency-and-subnormality/restricted-wreath.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [A fixed rational subset of the two-dimensional lamplighter group with undecidable membership](rational-subset-membership-lamplighter-z-squared.md)

## Expansion

Lohrey and Steinberg give a fixed rational subset $S$ of $L$ with undecidable membership (Theorem 10 of their paper on tilings and submonoids of metabelian groups, the [linked page](rational-subset-membership-lamplighter-z-squared.md)). Shafrir reduces membership in a fixed rational subset of a group $L$ to membership in a fixed finitely generated submonoid of $L \times H$ with $H$ an explicitly constructed finitely generated virtually abelian group (Theorem 8.1 of his paper, as the source recalls), so $G$ has undecidable submonoid membership. A good expansion adds and links a page for Shafrir's reduction and for Theorem 3.1 of the source. On the other side, the source deduces decidability in $L \times \mathbb{Z}^d$ from its decidability theorem for groups $\mathcal{Y} \rtimes \mathbb{Z}^n$.

## Sources

- R. Dong, "Submonoid membership in n-dimensional lamplighter groups and S-unit equations", in 52nd International Colloquium on Automata, Languages, and Programming (ICALP 2025), Leibniz International Proceedings in Informatics 334 (2025), article 154, https://doi.org/10.4230/LIPIcs.ICALP.2025.154; read in arXiv:2409.07077v4, whose numbering is used here (Theorem 3.1 and Corollary 3.2 of arXiv:2409.07077v4).
