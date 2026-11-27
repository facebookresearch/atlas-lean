# Decidability of submonoid membership does not pass to finite extensions

There are a group $G$ and a finite-index subgroup $\widetilde G \le G$ such that submonoid membership is decidable in $\widetilde G$ but undecidable in $G$.

There exist a group $G$ and a finite-index subgroup $\widetilde G \le G$ such that the submonoid membership problem is decidable in $\widetilde G$ and undecidable in $G$ (Corollary 3.2 of the source). Concretely $G = L \times H$ and $\widetilde G = L \times \mathbb{Z}^d$, where $L = (\mathbb{Z}/2\mathbb{Z}) \wr \mathbb{Z}^2$ is the two-dimensional lamplighter group, $H$ is a finitely generated virtually abelian group from Shafrir's construction, and $\mathbb{Z}^d$ is a finite-index subgroup of $H$.

The source proves (Theorem 3.1) that submonoid membership is decidable in every group $\mathcal{Y} \rtimes \mathbb{Z}^n$ with $\mathcal{Y}$ a finitely presented module over $\mathbb{F}_p[X_1^{\pm}, \dots, X_n^{\pm}]$, including the lamplighter groups $(\mathbb{Z}/p\mathbb{Z}) \wr \mathbb{Z}^n$, which gives decidability in $\widetilde G$.

## Depends on

- [Submonoid membership problem](submonoid-membership-problem.md)
- [Group](../../../group-basics/group.md)
- [Restricted wreath product](../../../soluble-finite-groups/solubility-nilpotency-and-subnormality/restricted-wreath.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [A fixed rational subset of the two-dimensional lamplighter group with undecidable membership](rational-subset-membership-lamplighter-z-squared.md)

## Expansion

Lohrey, Steinberg and Zetzsche give a rational subset $S$ of $L$ with undecidable membership. Shafrir reduces membership in a fixed rational subset of a group $L$ to membership in a fixed finitely generated submonoid of $L \times H$ with $H$ finitely generated virtually abelian, so $G$ has undecidable submonoid membership. Shafrir's reduction has no page here. On the other side, the source deduces decidability in $L \times \mathbb{Z}^d$ from its decidability theorem for groups $\mathcal{Y} \rtimes \mathbb{Z}^n$.

## Sources

- R. Dong, "Submonoid membership in n-dimensional lamplighter groups and S-unit equations", in 52nd International Colloquium on Automata, Languages, and Programming (ICALP 2025), Leibniz International Proceedings in Informatics 334 (2025), article 154, https://doi.org/10.4230/LIPIcs.ICALP.2025.154; read in arXiv:2409.07077v4, whose numbering is used here (Theorem 3.1 and Corollary 3.2 of arXiv:2409.07077v4).
