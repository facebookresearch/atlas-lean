# Positive one-relator groups with undecidable submonoid membership

For all integers $m, n \ge 2$ the positive one-relator group $G_{m,n} = \mathrm{Gp}\langle a, b \mid (ba^n)^m (a^n b)^m = 1 \rangle$ contains a fixed finitely generated submonoid in which membership is undecidable; so positive one-relator groups can have undecidable submonoid membership problem.

A one-relator group is positive if it has a presentation $\mathrm{Gp}\langle A \mid r = 1 \rangle$ in which the word $r$ contains no inverse letters. For integers $m, n \ge 2$ let

$$
G_{m,n} = \mathrm{Gp}\langle x, y \mid x^m y^n = y^n x^{-m} \rangle \cong \mathrm{Gp}\langle a, b \mid (ba^n)^m (a^n b)^m = 1 \rangle,
$$

the isomorphism sending $y \mapsto a$ and $x \mapsto ba^n$. Then $G_{m,n}$ is a positive one-relator group and there is a finitely generated submonoid $N$ of $G_{m,n}$ whose membership problem within $G_{m,n}$ is undecidable. In particular the submonoid membership problem of $G_{m,n}$ is undecidable (Theorem 3.8 of the source).

The source also shows (Lemma 3.2) that $G_{m,n}$ has decidable submonoid membership problem when $m = 1$ or $n = 1$. Since the monoid $\mathrm{Mon}\langle a, b \mid (ba^n)^m (a^n b)^m = 1 \rangle$ is the group $G_{m,n}$, it is a one-relation monoid with undecidable submonoid membership problem (Corollary 3.9).

## Depends on

- [Membership problem for a subset of a finitely generated group](membership-problem-for-a-subset.md)
- [Submonoid membership problem](submonoid-membership-problem.md)
- [Group](../../../group-basics/group.md)
- [One-relator group](../../coherence-of-one-relator-groups/one-relator-group.md)

## Proof depends on

None.

## Expansion

For $m, n \ge 2$ the source constructs an embedding of the right-angled Artin group $A(P_4)$ of the path with four vertices into $G_{m,n}$. Lohrey and Steinberg (J. Algebra 320 (2008)) proved that $A(P_4)$ contains a fixed finitely generated submonoid with undecidable membership problem; its image is the submonoid $N$. The positive presentation comes from the substitution $y = a$, $x = ba^n$, which turns the relator $x^m y^n x^m y^{-n}$ into $(ba^n)^m (a^n b)^m$. The result answers negatively whether positive one-relator groups, to whose submonoid membership problem Guba reduced the word problem of monoids $\mathrm{Mon}\langle a, b \mid bUa = a \rangle$, always have decidable submonoid membership problem.

## Sources

- I. Foniqi, R. D. Gray and C.-F. Nyberg-Brodda, "Membership problems for positive one-relator groups and one-relation monoids", Canadian Journal of Mathematics 78 (2026), no. 3, 802–841, https://doi.org/10.4153/S0008414X24000798; arXiv:2305.15672v2 (Lemma 3.2, Theorem 3.8 and Corollary 3.9 of arXiv:2305.15672v2).
