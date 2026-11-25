# Domain-independent calculus and relational algebra have the same expressive power

[Codd's theorem](codd-s-theorem-safe-range-calculus-equals-relational-algebra.md) states the equivalence of the
safe-range calculus with the relational algebra. This node states the stronger equivalence for the
domain-independent calculus.

Over a schema and constant set, with instances finite and the underlying domain infinite, the
domain-independent relational calculus and the relational algebra have the same expressive power: every
domain-independent calculus query is equivalent, under the natural semantics (which for such a query agrees with
the active-domain semantics), to a relational-algebra expression, and every relational-algebra expression is
equivalent to a domain-independent calculus query (Abiteboul, Hull and Vianu, Theorem 5.3.10).

Its proof translates a calculus query under the active-domain semantics into the algebra; the converse direction follows from Codd's theorem, since every safe-range query is domain independent.

## Depends on

- [Relational calculus and domain independence](relational-calculus-and-domain-independence.md)
- [Relational algebra queries](../relational-algebra/expr.md)

## Proof depends on

- [Codd's theorem: safe-range calculus equals relational algebra](codd-s-theorem-safe-range-calculus-equals-relational-algebra.md)

## Sources

- Foundations of Databases (Abiteboul, Hull, Vianu) — Abiteboul, Hull, Vianu; authors' free web edition (webdam.inria.fr/Alice), Definition 5.3.7, Lemma 5.3.8 (p. 79) and Theorem 5.3.10 (Equivalence Theorem) with Lemmas 5.3.11 and 5.3.12 (p. 80), all.pdf. <http://webdam.inria.fr/Alice/pdfs/all.pdf>
