# Homomorphism theorem for conjunctive queries with constants

Let $q(\bar x)$ and $q'(\bar x')$ be conjunctive queries of the same arity, possibly with constants. Then

$$q \subseteq q' \iff (q', \bar x') \to (q, \bar x).$$

Equivalently, let $G$ be a bijection from the variables of $q$ to constants that occur neither in $q$ nor in $q'$, extended
by the identity on constants; then $q \subseteq q'$ if and only if $G(\bar x) \in q'(G(A_q))$, that is, the frozen head
tuple of $q$ is an answer of $q'$ on the frozen body of $q$. For queries without constants this is the
[Chandra–Merlin containment criterion](../../../not-yet-classified/conjunctive-queries/contained-iff-hom.md).

## Depends on

- [Containment, equivalence and homomorphisms of conjunctive queries](containment-equivalence-and-homomorphisms-of-conjunctive-queries.md)
- [Answers of a conjunctive query](../answers-of-a-conjunctive-query.md)

## Proof depends on

- [Conjunctive queries are preserved under homomorphisms](../conjunctive-queries-are-preserved-under-homomorphisms.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Theorem 15.4 (Homomorphism Theorem, p. 119) and Corollary 15.6 (p. 120).
- A. K. Chandra and P. M. Merlin, "Optimal implementation of conjunctive queries in relational data bases", *Proceedings of the 9th ACM STOC*, 1977, pp. 77–90, as credited by the first source.
