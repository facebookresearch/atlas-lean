# CQ minimization (cores) and UCQ containment

This node collects minimization of conjunctive queries and containment of unions of conjunctive
queries, under set semantics over an infinite domain, with constants allowed and head variables fixed by
homomorphisms. Over a finite domain both results below can fail.

## Expansion

A sound expansion has separate pages for:

1. **Cores.** Every conjunctive query has an equivalent subquery that is minimal (no equivalent query
   with fewer atoms), obtained by folding along endomorphisms that fix the head (the cited source's Theorem 6.2.6);
   minimal equivalent conjunctive queries are isomorphic (its Proposition 6.2.9).
2. **UCQ containment.** For unions of conjunctive queries, $Q_1 \subseteq Q_2$ if and only if every disjunct
   of $Q_1$ is contained in some disjunct of $Q_2$ (Sagiv–Yannakakis, as given in the cited source's
   Exercise 6.14, whose separately handled case of a query equivalent to the empty query does not arise
   for conjunctive queries without equality atoms), so UCQ containment reduces to
   homomorphism tests between conjunctive queries, with the homomorphism from the containing query to
   the contained one.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Conjunctive queries, answers and canonical databases.
- Proof prerequisite: Chandra-Merlin homomorphism theorem.

## Sources

- Foundations of Databases (Abiteboul, Hull, Vianu) — Abiteboul, Hull, Vianu; authors' free web edition (webdam.inria.fr/Alice), Theorem 6.2.3, Theorem 6.2.6 (p. 119), Proposition 6.2.9 (p. 120), Exercises 6.12 and 6.14 (pp. 137–138) and the bibliographic notes crediting Chandra and Merlin. <http://webdam.inria.fr/Alice/pdfs/all.pdf>
- Optimal Implementation of Conjunctive Queries in Relational Data Bases (Chandra, Merlin), STOC 1977, as credited by Abiteboul, Hull and Vianu. <http://www.diag.uniroma1.it/degiacom/didattica/semingsoft/SIS05-06/materiale/1-query-congiuntive/riferimenti/chandra-merlin-1977.pdf>
