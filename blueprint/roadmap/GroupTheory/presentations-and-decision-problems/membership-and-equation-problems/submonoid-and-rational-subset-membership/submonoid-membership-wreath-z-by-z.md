# A fixed submonoid of Z wr Z with undecidable membership

The wreath product $\mathbb{Z} \wr \mathbb{Z}$ contains a fixed finitely generated submonoid whose membership problem is undecidable; consequently Thompson's group $F$ and Baumslag's finitely presented metabelian group contain such submonoids.

Let $\mathbb{Z} \wr \mathbb{Z}$ be the restricted wreath product, the semidirect product of the finitely supported functions $\mathbb{Z} \to \mathbb{Z}$ with $\mathbb{Z}$ acting by translation. There is a fixed finitely generated submonoid $M$ of $\mathbb{Z} \wr \mathbb{Z}$ whose membership problem is undecidable (Theorem 6 of the source).

Since $\mathbb{Z} \wr \mathbb{Z}$ embeds in both, Thompson's group $F$ and Baumslag's finitely presented metabelian group $\langle a, s, t \mid [s, t] = [a^t, a] = 1,\ a^s = a a^t \rangle$ contain finitely generated submonoids with undecidable membership problem (Corollary 1). By contrast, the source proves that $H \wr V$ has decidable [rational subset membership problem](rational-subset-membership-problem.md) for every finite group $H$ and virtually free group $V$, in particular for $H \wr \mathbb{Z}$ (Theorem 3).

## Depends on

- [Membership problem for a subset of a finitely generated group](membership-problem-for-a-subset.md)
- [Thompson's group $F$ by its standard presentation](../../../geometric-group-theory/branch-and-thompson-groups/thompson-s-group-f/thompson-f.md)
- [Restricted wreath product](../../../soluble-finite-groups/solubility-nilpotency-and-subnormality/restricted-wreath.md)
- [Group](../../../group-basics/group.md)
- [Submonoid membership problem](submonoid-membership-problem.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

There is a fixed two-counter machine $C$ for which it is undecidable whether $C$ reaches its final state with both counters zero from a configuration with counter values $m, n$ (Theorem 4). The source encodes the runs of $C$ by a fixed finitely generated submonoid of $\mathbb{Z}^{\Sigma} \wr \mathbb{Z}$, so that a computable element lies in the submonoid exactly when $C$ accepts $(m, n)$ (Theorem 5). The group $\mathbb{Z}^m \wr \mathbb{Z}$ is isomorphic to a subgroup of index $m$ in $\mathbb{Z} \wr \mathbb{Z}$, which transfers undecidability. By Cleary, $\mathbb{Z} \wr \mathbb{Z}$ embeds in Thompson's group $F$ and in Baumslag's metabelian group.

## Sources

- M. Lohrey, B. Steinberg and G. Zetzsche, "Rational subsets and submonoids of wreath products", Information and Computation 243 (2015), 191–204, https://doi.org/10.1016/j.ic.2014.12.014; read in arXiv:1302.2455v1 (Theorem 3 in Section 4 and Theorems 4, 5 and 6 and Corollary 1 in Section 5, with the llncs class numbering theorems and corollaries separately, of arXiv:1302.2455v1).
