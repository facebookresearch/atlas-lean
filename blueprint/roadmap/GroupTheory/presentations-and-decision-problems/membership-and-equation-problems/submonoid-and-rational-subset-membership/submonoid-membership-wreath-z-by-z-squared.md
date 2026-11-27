# A fixed submonoid of Z wr (Z x Z) with undecidable membership

The wreath product $\mathbb{Z} \wr (\mathbb{Z} \times \mathbb{Z})$ contains a fixed finitely generated submonoid whose membership problem is undecidable, although finitely generated metabelian groups have decidable subgroup membership problem.

Let $\mathbb{Z} \wr (\mathbb{Z} \times \mathbb{Z})$ be the restricted wreath product, the semidirect product of the group of finitely supported functions $\mathbb{Z}^2 \to \mathbb{Z}$ with $\mathbb{Z}^2$ acting by translation; it is a finitely generated metabelian group. There is a fixed finitely generated submonoid $N$ of $\mathbb{Z} \wr (\mathbb{Z} \times \mathbb{Z})$ such that the membership problem for $N$ within $\mathbb{Z} \wr (\mathbb{Z} \times \mathbb{Z})$ is undecidable; in particular its submonoid membership problem is undecidable (Corollary 5 of the source).

## Depends on

- [Membership problem for a subset of a finitely generated group](membership-problem-for-a-subset.md)
- [Submonoid membership problem](submonoid-membership-problem.md)
- [Group](../../../group-basics/group.md)
- [Restricted wreath product](../../../soluble-finite-groups/solubility-nilpotency-and-subnormality/restricted-wreath.md)
- [Metabelian groups](../../../geometric-group-theory/permutation-stability/metabelian.md)

## Proof depends on

None.

## Expansion

The main technical result (Theorem 4 of the source) is a free module $M$ of finite rank over $\mathbb{Z}[\mathbb{Z} \times \mathbb{Z}]$ with a fixed finitely generated subsemimodule (closed under addition and under the action of $\mathbb{Z} \times \mathbb{Z}$) whose membership problem is undecidable, proved by encoding a tiling problem for the plane. For a group $G$ and a $G$-module $M$, a subsemimodule $N$ with undecidable membership gives the submonoid $N \rtimes G$ of $M \rtimes G$ with undecidable membership (Proposition 2), and $M \rtimes (\mathbb{Z} \times \mathbb{Z})$ embeds in $\mathbb{Z} \wr (\mathbb{Z} \times \mathbb{Z})$. Submodule membership for free $\mathbb{Z}[\mathbb{Z} \times \mathbb{Z}]$-modules is decidable, which underlies the decidability of subgroup membership in metabelian groups (Romanovskii).

## Sources

- M. Lohrey and B. Steinberg, "Tilings and submonoids of metabelian groups", Theory of Computing Systems 48 (2011), no. 2, 411–427, https://doi.org/10.1007/s00224-010-9264-9; read in arXiv:0903.0648v1 (Proposition 2, Theorem 4 and Corollary 5 in Section 2 of arXiv:0903.0648v1; the llncs class numbers all statements with one counter).
