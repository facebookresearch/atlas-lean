# Membership in a recursively enumerable category of partitions can be undecidable

There is a recursively enumerable category of partitions in which no algorithm decides whether a given partition belongs to it, and no algorithm computes the number of its partitions with k upper and ℓ lower points.

**Theorem (Faroß and Volz).** There exists a recursively enumerable [category of partitions](categories-of-partitions.md) $\mathcal C$ such that:

1. the problem of deciding, for a partition $p$, whether $p\in\mathcal C$ is undecidable;
2. no Turing machine computes $|\mathcal C(k,\ell)|$ for all $k,\ell\in\mathbb N$.

(Theorem 1 of the introduction, combining Theorem 4.9 and Corollary 4.10 of the source.)

Without the requirement of recursive enumerability, undecidable membership is immediate, since there are uncountably many categories of partitions (Raum and Weber) but only countably many Turing machines. For the familiar categories, such as all partitions, pair partitions or non-crossing partitions, both problems are easy.

## Depends on

- [Categories of partitions](categories-of-partitions.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

- [Laws of a group](../../../GroupTheory/presentations-and-decision-problems/word-problem-for-groups/law-subgroup.md)
- [Varieties of groups](../../../GroupTheory/varieties-and-equations/axiomatizable-classes-of-groups/is-variety.md)

## Expansion

The proof reduces the identity problem for varieties of groups: Kleiman showed that some finitely based variety of groups has an undecidable set of identities, that is, of words $w$ in the free group $F_\infty$ on $x_1, x_2, \dots$ that are laws of every group in the variety (the source's Proposition 4.2). The identities of a variety form a fully invariant subgroup of $F_\infty$ (Proposition 4.3), recursively enumerable when the variety is finitely based (Remark 4.4). The map $x_n \mapsto a_1 a_{n+1}$ for $n \ge 1$ identifies $F_\infty$ with the subgroup $E$ of words of even length in the free product $\mathbb Z_2^{*\infty}$ of countably many copies of $\mathbb Z_2$, with generators $a_1, a_2, \dots$. Fully invariant subgroups of $E$ are $sS_\infty$-invariant normal subgroups of $\mathbb Z_2^{*\infty}$ (Proposition 4.6, which corrects Proposition 5.3 of Raum and Weber), and these correspond to hyperoctahedral categories of partitions by a theorem of Raum and Weber (Proposition 4.5). Each word $w$ then gives a partition $p(w)$ with $w$ an identity of the variety exactly when $p(w)\in\mathcal C$ (Lemma 4.8 and Theorem 4.9). Membership reduces to counting (Corollary 4.10): given $p \in \mathcal P(k,\ell)$ and $m = |\mathcal C(k,\ell)|$, enumerate $\mathcal C$ until $m$ distinct partitions of $\mathcal C(k,\ell)$ appear, and check whether $p$ is among them. A good expansion links pages for Kleiman's undecidability of the identity problem for varieties of groups, for the correspondence between fully invariant subgroups and varieties (Proposition 4.3), for Proposition 4.6 and for the Raum–Weber correspondence (Proposition 4.5).

## Sources

- N. Faroß and S. Volz, "Algorithmic problems in categories of partitions", in *Proceedings of the 2025 International Symposium on Symbolic and Algebraic Computation (ISSAC 2025)*, pp. 25–33, ACM, 2025, doi:[10.1145/3747199.3747543](https://doi.org/10.1145/3747199.3747543); read in arXiv:2502.05373v1 ([arXiv](https://arxiv.org/abs/2502.05373v1)): the main theorem in the introduction, and Proposition 4.2 (Kleiman), Proposition 4.3, Remark 4.4, Propositions 4.5 and 4.6, Lemma 4.8, Theorem 4.9 and Corollary 4.10 in Section 4 of arXiv:2502.05373v1.
- S. Raum and M. Weber, "Easy quantum groups and quantum subgroups of a semi-direct product quantum group", *Journal of Noncommutative Geometry* 9(4), 2016, pp. 1261–1293, doi:[10.4171/JNCG/223](https://doi.org/10.4171/JNCG/223); read as arXiv:1311.7630v2, <https://arxiv.org/abs/1311.7630v2>: Proposition 5.3, which states that $E$ is fully characteristic in $\mathbb Z_2^{*\infty}$; this fails, since the endomorphism with $a_1 \mapsto 1$ and $a_i \mapsto a_i$ for $i \ge 2$ sends $a_1 a_2 \in E$ to $a_2 \notin E$.
