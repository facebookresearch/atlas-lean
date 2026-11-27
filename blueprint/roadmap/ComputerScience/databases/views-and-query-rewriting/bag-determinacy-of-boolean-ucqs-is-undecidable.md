# Bag determinacy of Boolean unions of conjunctive queries is undecidable

Under multiset (bag) semantics, where a Boolean query returns the number of ways it is satisfied, no algorithm decides whether a finite set of Boolean unions of conjunctive queries determines another one. Under set semantics the problem is decidable, even for unary unions of conjunctive queries, and under bag semantics it is decidable for Boolean conjunctive queries.

**Setting (Kwiecień, Marcinkowski and Ostropolski-Nalewaja).** Structures are finite sets of facts over a finite relational schema, which may contain nullary predicates. For a Boolean conjunctive query $q$, identified with its frozen body, the bag answer on a structure $D$ is the natural number $q(D) = |\mathrm{Hom}(q, D)|$. A Boolean union of conjunctive queries $q_1 \vee \dots \vee q_k$ returns the multiset union of the answers, so its value on $D$ is $q_1(D) + \dots + q_k(D)$. A finite set $V$ of such queries *bag-determines* a query $q$, written $V \twoheadrightarrow_{\mathrm{bag}} q$, if for every pair of finite structures $D, D'$,

$$
\bigl(\forall v \in V:\ v(D) = v(D')\bigr) \implies q(D) = q(D').
$$

**Theorem (Kwiecień, Marcinkowski and Ostropolski-Nalewaja).** The following problem is undecidable: given a finite set $V$ of Boolean unions of conjunctive queries and a Boolean union of conjunctive queries $q$ over the same schema, does $V$ bag-determine $q$?

In contrast, the same paper proves that bag determinacy is decidable when $V$ and $q$ are Boolean conjunctive queries, and that for path queries bag determinacy coincides with set determinacy. Under set semantics, determinacy of Boolean (and even unary) unions of conjunctive queries is decidable.

## Depends on

- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Bag semantics of CQs: bag containment and bag equivalence](../conjunctive-queries/bag-semantics-of-cqs-bag-containment-and-bag-equivalence.md)
- [Determinacy of a query by views](determinacy-of-a-query-by-views.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The reduction is from the complement of Hilbert's tenth problem. For a polynomial given as a set of monomials over unknowns $x_1, \dots, x_n$, the schema has two nullary predicates $H, C$ and unary predicates $X_1, \dots, X_n$; the number of $X_i$-facts of a structure plays the role of $x_i$, and a monomial becomes a conjunctive query whose count is the value of the monomial (the encoding of Ioannidis and Ramakrishnan). The query is $q = H$, and the views use unions combining $H$ and $C$ (the "$p_1 \vee p_2$" trick) so that two structures with equal view answers agree on the unary predicates and can differ on $H$ only if the corresponding values of the unknowns are a root of the polynomial. Hence $V$ bag-determines $q$ exactly when the polynomial has no root in $\mathbb{N}$.

## Sources

- Jarosław Kwiecień, Jerzy Marcinkowski and Piotr Ostropolski-Nalewaja, "Determinacy of Real Conjunctive Queries. The Boolean Case", Proceedings of the 41st ACM SIGMOD-SIGACT-SIGAI Symposium on Principles of Database Systems (PODS 2022), pp. 347–358, 2022, <https://doi.org/10.1145/3517804.3524168>; Definition 1, Theorem 2 (main statement), Theorems 1 and 3, Section 2 (multiset semantics) and Appendix A (proof) of arXiv:2112.12742v1, read at <https://arxiv.org/abs/2112.12742v1>.
