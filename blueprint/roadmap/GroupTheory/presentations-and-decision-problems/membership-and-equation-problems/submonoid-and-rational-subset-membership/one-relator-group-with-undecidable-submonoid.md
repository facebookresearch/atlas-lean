# A one-relator group with a fixed finitely generated submonoid of undecidable membership

The one-relator group $\mathrm{Gp}\langle a, t \mid atat^{-1}a^{-1}ta^{-1}t^{-1} = 1 \rangle$ contains a fixed finitely generated submonoid whose membership problem is undecidable. Hence some one-relator groups have undecidable submonoid membership problem and undecidable rational subset membership problem.

Let

$$
G = \mathrm{Gp}\langle a, t \mid atat^{-1}a^{-1}ta^{-1}t^{-1} = 1 \rangle
$$

with canonical homomorphism $\pi\colon \{a, t, a^{-1}, t^{-1}\}^* \to G$. There is a finite set $W$ of words over $\{a, t, a^{-1}, t^{-1}\}$ such that the membership problem for the submonoid $M = \pi(W^*)$ within $G$ is undecidable: no algorithm decides, for a word $w$, whether $\pi(w) \in M$ (Theorem 2.4 of the source). Consequently the submonoid membership problem for $G$ is undecidable, and so is its rational subset membership problem (Corollary 2.5: there are one-relator groups with undecidable rational subset membership problem).

By contrast, every one-relator group has decidable word problem (Magnus); whether some one-relator group has undecidable subgroup membership problem is open.

## Depends on

- [Membership problem for a subset of a finitely generated group](membership-problem-for-a-subset.md)
- [Submonoid membership problem](submonoid-membership-problem.md)
- [Rational subset membership problem](rational-subset-membership-problem.md)
- [Group](../../../group-basics/group.md)
- [One-relator group](../../coherence-of-one-relator-groups/one-relator-group.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Lohrey and Steinberg (J. Algebra 320 (2008), Theorem 7) proved that the right-angled Artin group $A(P_4)$ of the path with four vertices contains a fixed finitely generated submonoid with undecidable membership problem. The source shows (Proposition 2.1) that $A(P_4)$ embeds in $G$, and more generally (Theorem 2.2) that the right-angled Artin group of every finite forest embeds in a one-relator group. The image $M$ of the Lohrey–Steinberg submonoid under the embedding is a finitely generated submonoid of $G$; membership in $M$ within $G$ restricts to membership within the image of $A(P_4)$, so it is undecidable. Every finitely generated submonoid is a rational subset, which gives the corollary.

## Sources

- R. D. Gray, "Undecidability of the word problem for one-relator inverse monoids via right-angled Artin subgroups of one-relator groups", Inventiones Mathematicae 219 (2020), no. 3, 987–1008, https://doi.org/10.1007/s00222-019-00920-2; arXiv:1902.03822v3 (Proposition 2.1, Theorem 2.2, Theorem 2.4 and Corollary 2.5 of arXiv:1902.03822v3).
