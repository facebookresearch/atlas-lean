# Some one-relator inverse monoid has undecidable word problem

There is a special one-relator inverse monoid $\mathrm{Inv}\langle A \mid w = 1 \rangle$, with $A$ finite, whose word problem is undecidable; it can be chosen $E$-unitary. This answers a question of Margolis, Meakin and Stephen from 1987.

There exist a finite set $A$ and a word $w \in (A \cup A^{-1})^*$ such that the inverse monoid $M = \mathrm{Inv}\langle A \mid w = 1 \rangle$ has undecidable word problem (Theorem 3.9 of the source). Moreover $M$ can be taken $E$-unitary (Corollary 3.10): the natural homomorphism from $M$ onto its maximal group image $\mathrm{Gp}\langle A \mid w = 1 \rangle$ is idempotent pure, that is, the preimage of the identity is exactly the set of idempotents of $M$.

In the example $A = \{a, z, t\}$ and $w = e \cdot azaz^{-1}a^{-1}za^{-1}z^{-1}$, where $e$ is an idempotent word (one that freely reduces to the empty word) built from $a$, $z$, $a^{-1}$, $z^{-1}$ and conjugates $tw_it^{-1}$ of words generating a submonoid with undecidable membership. The word $w$ is not freely reduced; whether $\mathrm{Inv}\langle A \mid w = 1 \rangle$ has decidable word problem for every freely reduced $w$ is open. By contrast, every special one-relation monoid $\mathrm{Mon}\langle A \mid w = 1 \rangle$ has decidable word problem (Adjan), and the group of units of the example has decidable word problem.

## Depends on

- [Inverse monoid and inverse semigroup presentations](inverse-monoid-and-semigroup-presentations.md)
- [Group](../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [A one-relator group with a fixed finitely generated submonoid of undecidable membership](../../presentations-and-decision-problems/membership-and-equation-problems/submonoid-and-rational-subset-membership/one-relator-group-with-undecidable-submonoid.md)

## Expansion

Let $G = \mathrm{Gp}\langle a, z \mid azaz^{-1}a^{-1}za^{-1}z^{-1} = 1 \rangle$, the one-relator group of Theorem 2.4 with $t$ renamed $z$, and let $W = \{w_1, \dots, w_k\}$ be words such that membership in the submonoid $T$ they generate is undecidable in $G$. The general construction (Theorem 3.8 of the source) gives a one-relator inverse monoid $M$ over $\{a, z, t\}$ such that, for a word $u$ over $\{a, z\}^{\pm 1}$, the element $tut^{-1}$ is right invertible in $M$ if and only if $u$ represents an element of $T$. A word $x$ is right invertible in $M$ exactly when $xx^{-1} = 1$ in $M$, so a solution of the word problem of $M$ would decide membership in $T$.

## Sources

- R. D. Gray, "Undecidability of the word problem for one-relator inverse monoids via right-angled Artin subgroups of one-relator groups", Inventiones Mathematicae 219 (2020), no. 3, 987–1008, https://doi.org/10.1007/s00222-019-00920-2; arXiv:1902.03822v3 (Theorem 3.8, Theorem 3.9 and Corollary 3.10 of arXiv:1902.03822v3).
