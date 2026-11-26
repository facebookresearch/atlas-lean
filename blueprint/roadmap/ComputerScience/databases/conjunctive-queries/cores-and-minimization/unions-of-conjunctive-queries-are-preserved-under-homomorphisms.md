# Unions of conjunctive queries are preserved under homomorphisms

Let $q = \varphi(\bar x)$ be a $k$-ary union of conjunctive queries in which the disjuncts may also contain equality
atoms $y = a$ between a variable and a constant, and let $C$ be the set of constants occurring in $\varphi$. For databases
$D, D'$ and tuples $\bar a \in \mathrm{Dom}(D)^k$, $\bar b \in \mathrm{Dom}(D')^k$, write $(D, \bar a) \to_C (D', \bar b)$
when some map $h : \mathrm{Dom}(D) \to \mathrm{Dom}(D')$ that is the identity on $C \cap \mathrm{Dom}(D)$ sends every fact of
$D$ to a fact of $D'$ and satisfies $h(\bar a) = \bar b$. Then $q$ is preserved under homomorphisms:

$$(D, \bar a) \to_C (D', \bar b) \text{ and } \bar a \in q(D) \implies \bar b \in q(D').$$

The converse direction for first-order queries on finite databases, that every first-order query preserved under
homomorphisms is equivalent to such a union, is a deep theorem stated without proof in the source.

## Depends on

- [Answers of a conjunctive query](../answers-of-a-conjunctive-query.md)
- [Containment of unions of conjunctive queries](containment-of-unions-of-conjunctive-queries.md)

## Proof depends on

- [Conjunctive queries are preserved under homomorphisms](../conjunctive-queries-are-preserved-under-homomorphisms.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Proposition 28.10 and the discussion of Theorem 28.11 (pp. 257–258).
