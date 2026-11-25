# Translation of relational algebra into safe-range calculus

Fix a database schema and the named relational algebra over it: selection by conditions built from
equalities with constants or between attributes by negation and conjunction, projection, natural join,
renaming along a permutation of the attributes, union and difference. For every algebra expression $E$
whose schema is defined there is a safe-range calculus query $\varphi_E$, with the constants of $E$, such
that $E(I) = \varphi_E(I)$ for every instance $I$ conforming to the schema, under active-domain semantics; since safe-range queries are
domain-independent, the equality also holds under natural semantics. The translation is compositional
and $\lVert \varphi_E \rVert$ is polynomial in $\lVert E \rVert$ when expressions and formulas are encoded as syntax trees.

## Depends on

- [Relational algebra queries](../relational-algebra/expr.md)
- [Relational calculus and domain independence](relational-calculus-and-domain-independence.md)
- [Schema of a query](../relational-algebra/schema.md)
- [Databases conforming to a schema](../relational-algebra/conforms.md)
- [Selection conditions](../relational-algebra/cond.md)

## Sources

- Foundations of Databases (Abiteboul, Hull, Vianu) — Abiteboul, Hull, Vianu; authors' free web edition (webdam.inria.fr/Alice), Lemma 5.3.11 and its proof (p. 80, for the unnamed algebra), the remark that the query it constructs is safe range (p. 85), and Theorem 5.4.6 (p. 86). <http://webdam.inria.fr/Alice/pdfs/all.pdf>
