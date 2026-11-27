# Equivalence of conjunctive queries is NP-complete

Given two tableau queries $q$ and $q'$ over the same schema, deciding whether $q \equiv q'$ is NP-complete, with the
two queries as the input; it remains NP-complete for single-relation typed tableau queries without constants
(Abiteboul, Hull and Vianu, Theorem 6.2.10(b), credited there to Chandra and Merlin). Membership holds because
$q \equiv q'$ means containment in both directions, and $q \subseteq q'$ holds iff the summary of $q$ is an answer of
$q'$ on the tableau of $q$; hardness is by reduction from exact cover.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: conjunctive (tableau) queries and their containment and equivalence.
- Proof prerequisites: NP-completeness of containment of conjunctive queries; the homomorphism theorem for tableau
  queries.

## Sources

- Foundations of Databases (Abiteboul, Hull, Vianu) — Abiteboul, Hull, Vianu; authors' free web edition (webdam.inria.fr/Alice), Corollaries 6.2.4 and 6.2.5 (p. 117), Theorem 6.2.10 (p. 120) and the bibliographic notes to Chapter 6. <http://webdam.inria.fr/Alice/pdfs/all.pdf>
