# Naive evaluation computes certain answers for UCQs

Over an infinite set of constants, for every union of conjunctive queries $q$ and every naive table $D$,
evaluating $q$ on $D$ with the marked
nulls treated as pairwise distinct constants distinct from all other constants, and then keeping only the
null-free output tuples, yields exactly the certain answers of $q$ on $D$ under closed-world semantics. The
infinite supply of constants is needed: with constants $1, 2$ only, $R = \{(\bot)\}$, $S = \{(1), (2)\}$
and the Boolean query $\exists x\, (R(x) \wedge S(x))$, naive evaluation returns false although every
valuation makes the query true. The theorem is distinct from Libkin's Proposition 3.2, which states that
SQL's three-valued evaluation, in which every comparison involving a null is unknown, returns tuples of
which every null-free one is a certain answer on such queries.

## Depends on

- [Incomplete databases, possible worlds and certain answers](incomplete-databases-possible-worlds-and-certain-answers.md)
- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Containment of unions of conjunctive queries](../conjunctive-queries/cores-and-minimization/containment-of-unions-of-conjunctive-queries.md)

## Proof depends on

- [Homomorphism theorem for conjunctive queries with constants](../conjunctive-queries/cores-and-minimization/homomorphism-theorem-for-conjunctive-queries-with-constants.md)
- [Unions of conjunctive queries are preserved under homomorphisms](../conjunctive-queries/cores-and-minimization/unions-of-conjunctive-queries-are-preserved-under-homomorphisms.md)
- [Naive evaluation is exact for homomorphism-preserved queries](naive-evaluation-is-exact-for-homomorphism-preserved-queries.md)

## Sources

- SQL's Three-Valued Logic and Certain Answers (Libkin), ACM TODS 2016 — ACM TODS 41(1) 2016, authors' copy, Section 3: Definition 3.1, the inclusion of the certain answers in the naive evaluation, and the certainty guarantee of naive evaluation for unions of conjunctive queries (pp. A:6–A:7); Proposition 3.2 for SQL's evaluation. <https://homepages.inf.ed.ac.uk/libkin/papers/tods16.pdf>
- Incomplete Information in Relational Databases (Imielinski, Lipski), JACM 1984 — JACM 31(4) 1984, Section 6 (V-tables over infinite attribute domains), Theorem 6.1, and Section 9 (closed-world interpretation), Theorem 9.1. <https://cs.uwaterloo.ca/~david/kbdb/imielinskilipski.pdf>
