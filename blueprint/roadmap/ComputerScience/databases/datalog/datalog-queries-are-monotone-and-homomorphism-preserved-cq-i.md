# Datalog queries are monotone and homomorphism-preserved; CQ-in-Datalog containment

This node collects homomorphism preservation for positive Datalog and containment of conjunctive
queries in Datalog programs.

## Expansion

A sound expansion has separate pages for:

1. **Monotonicity and homomorphism preservation.** Every Datalog program $P$ is monotone, and for every
   map $h$ on the domain that fixes the constants of $P$ and satisfies $h(I) \subseteq J$,
   $h(P(I)) \subseteq P(J)$. For constant-free programs and arbitrary maps this is the cited textbook's
   Lemma 12.5.1; for programs with constants it fails for arbitrary maps (its Exercise 12.21), which is
   why the map must fix them.
2. **Non-monotone queries.** Consequently no Datalog program expresses a query that is not monotone,
   even one computable in polynomial time.
3. **Canonical-database characterization.** A conjunctive query $q$ is contained in a Datalog program $P$
   if and only if the frozen head tuple of $q$ belongs to $P$ applied to the canonical database of $q$; hence
   containment is decidable.
4. **Complexity**, as a separate page: the cited source reports, citing earlier work, that containment of
   a conjunctive query in a recursive Datalog program is EXPTIME-complete when the program is part of the
   input, and NP-complete when the arity of the programs is bounded.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Conjunctive queries, answers and canonical databases.
- Proof prerequisite: Chandra-Merlin homomorphism theorem.

## Depends on

- [Datalog programs and the immediate consequence operator](datalog-programs-and-the-immediate-consequence-operator.md)
- [Least model equals least fixpoint for Datalog](least-model-equals-least-fixpoint-for-datalog.md)

## Sources

- On the Equivalence of Recursive and Nonrecursive Datalog Programs (Chaudhuri, Vardi), PODS 1992 — PODS 1992 / JCSS, author copy, Introduction: containment of a conjunctive query in a recursive program is decidable and EXPTIME-complete, citing earlier work, and NP-complete for bounded arity. <https://www.cs.rice.edu/~vardi/papers/pods92rj.pdf>
- Foundations of Databases (Abiteboul, Hull, Vianu) — Abiteboul, Hull, Vianu; authors' free web edition (webdam.inria.fr/Alice), Lemma 12.5.1 (p. 301) and Exercise 12.21. <http://webdam.inria.fr/Alice/pdfs/all.pdf>
