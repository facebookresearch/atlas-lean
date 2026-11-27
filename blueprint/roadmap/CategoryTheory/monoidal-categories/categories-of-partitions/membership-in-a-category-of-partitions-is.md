# Membership in a recursively enumerable category of partitions can be undecidable

There is a recursively enumerable category of partitions in which no algorithm decides whether a given partition belongs to it, and no algorithm computes the number of its partitions with k upper and ℓ lower points.

**Theorem (Faroß and Volz).** There exists a recursively enumerable [category of partitions](categories-of-partitions.md) $\mathcal C$ such that:

1. the problem of deciding, for a partition $p$, whether $p\in\mathcal C$ is undecidable;
2. no Turing machine computes $|\mathcal C(k,\ell)|$ for all $k,\ell\in\mathbb N$.

(Theorem 1 of the introduction, combining Theorem 4.9 and Corollary 4.10 of the source.)

Without the requirement of recursive enumerability the statement is immediate, since there are uncountably many categories of partitions (Raum and Weber) but only countably many Turing machines. For the familiar categories, such as all partitions, pair partitions or non-crossing partitions, both problems are easy.

## Depends on

- [Categories of partitions](categories-of-partitions.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

None.

## Expansion

The proof reduces the identity problem for varieties of groups: Kleiman showed that some finitely based variety of groups has an undecidable set of identities, that is, of words $w$ in the free group $F_\infty$ that are laws of every group in the variety. The identities of a variety form a fully invariant subgroup of $F_\infty$, which is identified with the subgroup $E$ of words of even length in the free product $\mathbb Z_2^{*\infty}$ of countably many copies of $\mathbb Z_2$ via $x_n\mapsto a_1a_{n+1}$. Fully invariant subgroups of $E$ are $sS_\infty$-invariant normal subgroups of $\mathbb Z_2^{*\infty}$, which correspond to hyperoctahedral categories of partitions by a theorem of Raum and Weber, in a form the source corrects. Each word $w$ then gives a partition $p(w)$ with $w$ an identity of the variety exactly when $p(w)\in\mathcal C$, and $\mathcal C$ is recursively enumerable because the identities of a finitely based variety are. Counting reduces membership, since $p\in\mathcal C$ can be decided once $|\mathcal C(k,\ell)|$ is known, by enumerating $\mathcal C$ until that many partitions of the size of $p$ appear. A good expansion links pages for Kleiman's undecidability of the identity problem for varieties of groups and for the Raum–Weber correspondence; neither has a page yet. The [laws of a group](../../../GroupTheory/presentations-and-decision-problems/word-problem-for-groups/law-subgroup.md) are defined on their own page.

## Sources

- N. Faroß and S. Volz, "Algorithmic problems in categories of partitions", in *Proceedings of the 2025 International Symposium on Symbolic and Algebraic Computation (ISSAC 2025)*, pp. 25–33, ACM, 2025, doi:[10.1145/3747199.3747543](https://doi.org/10.1145/3747199.3747543); read in arXiv:2502.05373v1 ([arXiv](https://arxiv.org/abs/2502.05373v1)): the main theorem in the introduction, and Proposition 4.2 (Kleiman), Proposition 4.5, Lemma 4.8, Theorem 4.9 and Corollary 4.10 in Section 4 of arXiv:2502.05373v1.
