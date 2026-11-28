# The universal theory of groups of a fixed large odd composite exponent is undecidable

The universal theory of torsion groups is undecidable (Slobodskoi), and so is the universal theory of groups of any fixed sufficiently large odd non-prime exponent, and of $p$-groups for each fixed prime $p \ne 2$.

A universal sentence in the first-order language of groups is a sentence $\forall x_1 \dots \forall x_k\, \Phi$ with $\Phi$ quantifier-free; the universal theory $\mathrm{Th}_\forall(\mathcal{C})$ of a class $\mathcal{C}$ of groups is the set of universal sentences true in every group of $\mathcal{C}$, and it is decidable if some algorithm decides membership in it. The universal theory of each of the following classes is undecidable (Theorem 1.2 of the source): (a) the class of torsion groups (Slobodskoi); (b) the class of groups of any fixed sufficiently large odd exponent that is not prime (the source says "non-simple"); (c) the class of $p$-groups, for every fixed prime $p \ne 2$.

Theorem 1.2 is a corollary of a more general statement: if a class $\mathcal{C}$ of groups contains the Burnside variety $\mathfrak{B}_n$ of groups of exponent dividing $n$ for some odd non-prime $n > 2^{48}$, then $\mathrm{Th}_\forall(\mathcal{C})$ is undecidable (Theorem 2.4). The source also proves $\mathrm{Th}_\forall(\mathcal{T}) \subsetneq \mathrm{Th}_\forall(\mathcal{F})$ for the classes $\mathcal{T}$ of torsion groups and $\mathcal{F}$ of finite groups, answering a question of Dyson (Theorem 1.1).

## Depends on

- [Free Burnside groups](../../periodic-and-locally-finite-groups/free-burnside-groups/free-burnside-group.md)
- [Group](../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Varieties of groups](../axiomatizable-classes-of-groups/is-variety.md)
- [The first-order language of groups](../../../Logic/model-theory/first-order-language-of-groups/group-language.md)
- [Complete theory of a first-order structure](../../../Logic/first-order-logic/theory-of-structure.md)

## Proof depends on

None.

## Expansion

The proof of Theorem 2.4 combines two results the source quotes. Kharlampovich: for $n = pq$ with $p \ge 3$ prime and $q$ having an odd divisor at least $665$, some quotient $B(m, n)/N$ of a free Burnside group by the normal closure of finitely many elements has undecidable word problem (Theorem 2.3 of the source). Olshanskii and Sapir, simplified by Ivanov: for odd sufficiently large $n$, $B(m, n)$ embeds in a finitely presented group $G$ such that (a) $B(m, n)$ is a Q-subgroup (one with the congruence extension property) of $G$, and (b) the natural map $\varepsilon\colon G \to H = G/G^n$ is injective on $B(m, n)$ and $\varepsilon(B(m, n))$ is a Q-subgroup of $H$ (Theorem 2.1 of the source). With a finite presentation $\langle x_1, \dots, x_s \mid U_1, \dots, U_p \rangle$ of $G_1 = G / \langle\!\langle N \rangle\!\rangle$, a word $V$ in the generators of $B(m, n)/N$ is trivial exactly when the universal sentence $\forall \bar x\, (U_1 = 1 \wedge \dots \wedge U_p = 1 \to \hat V(\bar x) = 1)$ lies in $\mathrm{Th}_\forall(\mathcal{C})$: if it does, it holds in $H_1 = H/\langle \varepsilon(N) \rangle^H$, which lies in $\mathfrak{B}_n$ and, by part (b), contains the image of $\varepsilon(B(m, n))$, a copy of $\varepsilon(B(m, n))/\varepsilon(N) \cong B(m, n)/N$, so $V = 1$; if it fails in some group of $\mathcal{C}$, then $V \ne 1$. Clause (a), for torsion groups, is Slobodskoi's result. A good expansion links pages for the theorems of Kharlampovich and of Olshanskii and Sapir.

## Sources

- D. Osin, "On the universal theory of torsion and lacunary hyperbolic groups", Groups – Complexity – Cryptology 1 (2009), no. 2 (the publisher metadata records no page range), https://doi.org/10.1515/GCC.2009.311; read in arXiv:0903.3978v2 (Theorems 1.1, 1.2, 2.1, 2.3 and 2.4 and Lemma 3.1 of arXiv:0903.3978v2).
