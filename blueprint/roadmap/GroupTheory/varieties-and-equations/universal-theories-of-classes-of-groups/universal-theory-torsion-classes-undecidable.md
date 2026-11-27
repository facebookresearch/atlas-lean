# The universal theory of groups of a fixed large odd composite exponent is undecidable

The universal theory of torsion groups is undecidable (Slobodskoi), and so is the universal theory of groups of any fixed sufficiently large odd non-prime exponent, and of $p$-groups for each fixed prime $p \ne 2$.

A universal sentence in the first-order language of groups is a sentence $\forall x_1 \dots \forall x_k\, \Phi$ with $\Phi$ quantifier-free; the universal theory $\mathrm{Th}_\forall(\mathcal{C})$ of a class $\mathcal{C}$ of groups is the set of universal sentences true in every group of $\mathcal{C}$, and it is decidable if some algorithm decides membership in it. The universal theory of each of the following classes is undecidable (Theorem 1.2 of the source): (a) the class of torsion groups (Slobodskoi); (b) the class of groups of any fixed sufficiently large odd non-simple exponent; (c) the class of $p$-groups, for every fixed prime $p \ne 2$.

Theorem 1.2 is a corollary of a more general statement: if a class $\mathcal{C}$ of groups contains the Burnside variety $\mathfrak{B}_n$ of groups of exponent dividing $n$ for some odd non-prime $n > 2^{48}$, then $\mathrm{Th}_\forall(\mathcal{C})$ is undecidable (Theorem 2.4). The source also proves $\mathrm{Th}_\forall(\mathcal{T}) \subsetneq \mathrm{Th}_\forall(\mathcal{F})$ for the classes $\mathcal{T}$ of torsion groups and $\mathcal{F}$ of finite groups, answering a question of Dyson (Theorem 1.1).

## Depends on

- [Free Burnside groups](../../periodic-and-locally-finite-groups/free-burnside-groups/free-burnside-group.md)
- [Group](../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](../../presentations-and-decision-problems/word-problem-for-groups/novikov-unsolvable.md)

## Expansion

Kharlampovich showed that for $n = pq$ with $p \ge 3$ prime and $q$ having an odd divisor at least $665$, some quotient of a free Burnside group $B(m, n)$ by the normal closure of finitely many elements has undecidable word problem (Theorem 2.3 of the source). A universal sentence $\forall \bar x\, (\bigwedge_i r_i(\bar x) = 1 \to w(\bar x) = 1)$ holds in all groups of exponent $n$ exactly when $w = 1$ in that quotient, so the universal theory of $\mathfrak{B}_n$ encodes an undecidable word problem; Slobodskoi's lemma covers theories between those of torsion groups and finite groups.

## Sources

- D. Osin, "On the universal theory of torsion and lacunary hyperbolic groups", Groups – Complexity – Cryptology 1 (2009), no. 2 (the publisher metadata records no page range), https://doi.org/10.1515/GCC.2009.311; read in arXiv:0903.3978v2 (Theorems 1.1, 1.2, 2.3 and 2.4 and Lemma 3.1 of arXiv:0903.3978v2).
