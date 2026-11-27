# Inequality, negation, difference, union and equality are not expressible by conjunctive queries

None of the following first-order queries is equivalent to a conjunctive query (over all finite databases of its
schema), where $a$ is a constant and $R, S, P, Q$ are relation names:

1. $\exists x \exists y\, (R(x, y) \wedge x \ne y)$ and $\exists x\, (S(x) \wedge x \ne a)$, since they are not preserved
   under homomorphisms that fix the constants $C$ of a candidate conjunctive query: for distinct elements $d, e$ outside
   $C \cup \{a\}$ and any $c$, $\{R(d, e)\} \to_C \{R(c, c)\}$ and $\{S(d)\} \to_{C} \{S(a)\}$, while the first database satisfies the query
   and the second does not;
2. $\neg P(a)$ and $\exists x\, (P(x) \wedge \neg Q(x))$, since they are not monotone;
3. $\exists x\, (R(x) \vee S(x))$ for unary $R$ and $S$, and $\exists x \exists y\, (x = y)$ over the schema $\{R, S\}$
   with $R$ and $S$ unary, since they are not preserved under direct products: $\{R(a)\}$ and $\{S(a)\}$ satisfy
   them while their direct product is empty; for a candidate with constants, a conjunctive query true on both
   $\{R(a)\}$ and $\{S(a)\}$ can contain neither an $R$ atom nor an $S$ atom, so its body would be empty.

## Depends on

- [Answers of a conjunctive query](answers-of-a-conjunctive-query.md)

## Proof depends on

- [Conjunctive queries are preserved under homomorphisms](conjunctive-queries-are-preserved-under-homomorphisms.md)
- [Conjunctive queries are monotone](conjunctive-queries-are-monotone.md)
- [Boolean conjunctive queries are preserved under direct products](boolean-conjunctive-queries-are-preserved-under-direct-products.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, the list of inexpressibility results following Proposition 13.9 (p. 107).
