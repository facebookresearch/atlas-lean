# Projected CQ prefix enumeration and correctness

Let $Q$ be a safe acyclic conjunctive query over a finite instance, with $h \ge 0$ distinct head variables in a
fixed order and active domain of size $A$. The prefix algorithm first tests whether $Q$ has an answer; it
then extends each retained prefix (a partial assignment to the first $j$ head variables) by every
active-domain value and retains exactly the extensions for which the residual query, obtained by fixing
these values (filtering relations and deleting the fixed variables, which preserves the join tree), is
nonempty. Then the retained prefixes at depth $j$ are exactly the restrictions of answers to the first $j$
head variables, and at depth $h$ reconstructing the head (including constants and repeated head terms)
lists every answer exactly once; for $h = 0$ the output is the empty tuple exactly when $Q$ is true. This is
an original derivation from the acyclic Boolean evaluation result, not a theorem quoted from the cited
source.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Conjunctive queries, answers and canonical databases.

## Depends on

- [Characterizations of acyclic database schemas](characterizations-of-acyclic-database-schemas.md)

## Proof depends on

- [Yannakakis' algorithm for acyclic join queries](yannakakis-algorithm-for-acyclic-join-queries.md)

## Sources

- Hypertree Decompositions and Tractable Queries (Gottlob, Leone, Scarcello), arXiv cs/9812022v1 manuscript — Authors' arXiv manuscript cs/9812022v1, Section 1.2, item (3) (output-polynomial evaluation of acyclic queries, credited to Yannakakis), as context; the prefix enumerator is not the source's algorithm. <https://arxiv.org/pdf/cs/9812022>
