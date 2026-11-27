# Some positive two-relator inverse monoid has undecidable word problem

There are a finite alphabet $A$ and nonempty positive words $u, v \in A^+$ such that the inverse monoid $\mathrm{Inv}\langle A \mid u = 1, v = 1 \rangle$ has undecidable word problem; the example can be chosen $E$-unitary.

Precisely, there exist a finite set $A$ and words $u, v \in A^+$ such that the special inverse monoid $M = \mathrm{Inv}\langle A \mid u = 1, v = 1 \rangle$ has undecidable word problem, and $M$ can be chosen $E$-unitary: the natural homomorphism onto its maximal group image $\mathrm{Gp}\langle A \mid u = 1, v = 1 \rangle$ has the idempotents of $M$ as the preimage of the identity (Theorem 7.1 of the source).

The groups $\mathrm{Gp}\langle A \mid u = 1, v = 1 \rangle$ arising in the proof are isomorphic to one-relator groups and so have decidable word problem. Whether every positive one-relator inverse monoid $\mathrm{Inv}\langle A \mid w = 1 \rangle$ with $w \in A^+$ has decidable word problem is open.

## Depends on

- [Inverse monoid and inverse semigroup presentations](inverse-monoid-and-semigroup-presentations.md)
- [Group](../../group-basics/group.md)

## Proof depends on

- [Positive one-relator groups with undecidable submonoid membership](../../presentations-and-decision-problems/membership-and-equation-problems/submonoid-and-rational-subset-membership/positive-one-relator-undecidable-submonoid.md)

## Expansion

The source proves a general encoding (Theorem 7.4): for a positive one-relator group $G$ and a finitely generated submonoid $Q$ of $G$, it builds a positive two-relator inverse monoid, $E$-unitary with maximal group image $G * \mathbb{Z}$, whose word problem decides membership in $Q$ within $G$. Applied to a group $G_{m,n}$ with $m, n \ge 2$ and a submonoid with undecidable membership, this gives the theorem. For positive words $u, v$ one has $\mathrm{Inv}\langle A \mid uv^{-1} = 1 \rangle \cong \mathrm{Inv}\langle A, t \mid ut = 1, vt = 1 \rangle$, and by Ivanov, Margolis and Meakin the word problem for one-relation monoids reduces to inverse monoids of this two-relator form, which motivates the positive two-relator case.

## Sources

- I. Foniqi, R. D. Gray and C.-F. Nyberg-Brodda, "Membership problems for positive one-relator groups and one-relation monoids", Canadian Journal of Mathematics 78 (2026), no. 3, 802–841, https://doi.org/10.4153/S0008414X24000798; arXiv:2305.15672v2 (Theorem 7.1 and Theorem 7.4 of arXiv:2305.15672v2).
