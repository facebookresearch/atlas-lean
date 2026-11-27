# Membership problem for a subset of a finitely generated group

For a fixed subset $S$ of a finitely generated group $G$, the membership problem for $S$ within $G$ asks for an algorithm that decides, for a word over a finite generating set and its inverses, whether the element it represents lies in $S$.

Let $G$ be a group, $X$ a finite set and $\pi\colon (X \cup X^{-1})^* \to G$ the monoid homomorphism extending a map $X \to G$ whose image generates $G$ as a group; here $X^{-1}$ is a set of formal inverses disjoint from $X$, with $\pi(x^{-1}) = \pi(x)^{-1}$. For a subset $S \subseteq G$ the membership problem for $S$ within $G$ is the decision problem

- input: a word $w \in (X \cup X^{-1})^*$;
- question: is $\pi(w) \in S$?

It is decidable when the set $\{w \in (X \cup X^{-1})^* : \pi(w) \in S\}$ is recursive, and undecidable otherwise. The subset $S$ is fixed: it is not part of the input. Decidability does not depend on the choice of the finite generating set, since words over one finite generating set are effectively rewritten over another.

For $S = \{1\}$ this is the word problem of $G$; for a finitely generated subgroup $S$ it is the membership (generalized word) problem of that subgroup.

## Depends on

- [Group](../../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The uniform problems on the pages [Submonoid membership problem](submonoid-membership-problem.md) and [Rational subset membership problem](rational-subset-membership-problem.md) take the subset as part of the input, given by finitely many words or by a finite automaton. If the membership problem for one fixed finitely generated submonoid is undecidable, then so is the uniform submonoid membership problem, by fixing that part of the input.

## Sources

- R. D. Gray, "Undecidability of the word problem for one-relator inverse monoids via right-angled Artin subgroups of one-relator groups", Inventiones Mathematicae 219 (2020), no. 3, 987–1008, https://doi.org/10.1007/s00222-019-00920-2; arXiv:1902.03822v3 (Section 2, the definitions preceding Theorem 2.4 of arXiv:1902.03822v3).
