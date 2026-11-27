# Containment, equivalence and homomorphisms of conjunctive queries

Let $q(\bar x)$ and $q'(\bar x')$ be conjunctive queries of the same arity over a schema, possibly with constants, as in
[answers of a conjunctive query](../answers-of-a-conjunctive-query.md), and write $A_q$ for the set of body atoms of $q$.
Then $q$ is contained in $q'$, written $q \subseteq q'$, when $q(D) \subseteq q'(D)$ for every database $D$, and $q$ and
$q'$ are equivalent, $q \equiv q'$, when $q \subseteq q'$ and $q' \subseteq q$.

For sets of atoms $S, S'$ over constants and variables, finite or infinite, and tuples $\bar u, \bar v$ of the same length
over their terms, a homomorphism from $(S, \bar u)$ to $(S', \bar v)$ is a map $h$ from the terms of $S$ and $\bar u$ to terms that is
the identity on constants, sends every atom $R(\bar w) \in S$ to an atom $R(h(\bar w)) \in S'$, and satisfies
$h(\bar u) = \bar v$; write $(S, \bar u) \to (S', \bar v)$ when one exists, and $(q', \bar x') \to (q, \bar x)$ for
$(A_{q'}, \bar x') \to (A_q, \bar x)$. Two conjunctive queries $q(\bar x)$ and $q'(\bar x')$ are isomorphic when some
bijection between their variables, extended by the identity on constants, is a homomorphism from $(A_q, \bar x)$ to
$(A_{q'}, \bar x')$ whose inverse is a homomorphism from $(A_{q'}, \bar x')$ to $(A_q, \bar x)$.

## Depends on

- [Answers of a conjunctive query](../answers-of-a-conjunctive-query.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Chapter 15 (containment and equivalence, the notation $(q', \bar x') \to (q, \bar x)$, p. 119) and Chapter 16 (isomorphic conjunctive queries, before Proposition 16.7, p. 127).
