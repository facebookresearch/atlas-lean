# Equivalence of conjunctive queries is NP-complete

Given two tableau queries $q$ and $q'$ over the same schema, deciding whether $q \equiv q'$ is NP-complete, with the
two queries as the input; it remains NP-complete for single-relation typed tableau queries without constants
(Abiteboul, Hull and Vianu, Theorem 6.2.10(b), credited there to Chandra and Merlin). Membership holds because
$q \equiv q'$ means containment in both directions, and $q \subseteq q'$ holds iff the summary of $q$ is an answer of
$q'$ on the tableau of $q$; hardness is by reduction from exact cover.

## Depends on

- [Containment, equivalence and homomorphisms of conjunctive queries](cores-and-minimization/containment-equivalence-and-homomorphisms-of-conjunctive-queries.md)
- [Answers of a conjunctive query](answers-of-a-conjunctive-query.md)
- [NP-complete decision problems](../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [CONJUNCTIVE QUERY CONTAINMENT is NP-complete](../../../TheoryOfComputation/np-completeness/databases-and-concurrency/databases-and-concurrency/conjunctive-query-containment-np-complet.md)
- [Homomorphism theorem for conjunctive queries with constants](cores-and-minimization/homomorphism-theorem-for-conjunctive-queries-with-constants.md)
- [EXACT COVER is NP-complete](../../../TheoryOfComputation/np-completeness/set-systems-and-location/exact-cover/exact-cover-np-complete.md)

## Sources

- Foundations of Databases (Abiteboul, Hull, Vianu) — Abiteboul, Hull, Vianu; authors' free web edition (webdam.inria.fr/Alice), Corollaries 6.2.4 and 6.2.5 (pp. 117–118), Theorem 6.2.10 (p. 120) and the bibliographic notes to Chapter 6. <http://webdam.inria.fr/Alice/pdfs/all.pdf>
