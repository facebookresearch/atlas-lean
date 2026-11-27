# Zero-one law consequence: parity of the domain is not a relational-calculus query

In the active-domain zero-one framework of Abiteboul, Hull and Vianu (Section 17.3), sentences are total,
constant-free Boolean queries, and $\mu_n(q)$ is the fraction of instances $I$ with active domain
$\{1, \dots, n\}$ that satisfy $q$. For the schema with one unary relation $R$ there is exactly one such
instance for each $n \ge 0$, namely $R = \{1, \dots, n\}$. For the query EVEN, true when $\lvert R \rvert$
is even, $\mu_n(\mathrm{EVEN})$ is $1$ for even $n$ and $0$ for odd $n$, so it has no limit. Assuming the
zero-one laws of the source (17.3.7 for CALC and 17.3.8 for constant-free while sentences defined on all
instances) hold for this schema, EVEN is not expressible in constant-free CALC or relational algebra, nor
in constant-free while or fixpoint queries without order. The zero-one law for this schema is an external
prerequisite: the source proves it for one loopless binary relation and leaves the general case as an
exercise; the ordinary first-order zero-one law page is not the same measure.

## Expansion

This node states a precise result. The first source states this consequence for EVEN in Section 17.3, in
the paragraph after Definition 17.3.4.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Proof prerequisite: the zero-one law for the active-domain measure on this schema (17.3.7 and 17.3.8 of the source).

## Depends on

- [Relational calculus and domain independence](../relational-calculus/relational-calculus-and-domain-independence.md)

## Related topics

- [Zero-one law for first-order logic](../../../Logic/model-theory/zero-one-law-for-first-order-logic/zero-one-law.md)

## Sources

- Foundations of Databases (Abiteboul, Hull, Vianu) — Abiteboul, Hull, Vianu; authors' free web edition (webdam.inria.fr/Alice), Section 17.3: Definitions 17.3.3–17.3.4 and the EVEN paragraph (p. 441), Theorems 17.3.7–17.3.8 (p. 444), Exercise 17.19. <http://webdam.inria.fr/Alice/pdfs/all.pdf>
- Elements of Finite Model Theory (Libkin) — Leonid Libkin. <https://www.cs.utoronto.ca/~libkin/fmt/fmt.pdf> Background reference.
