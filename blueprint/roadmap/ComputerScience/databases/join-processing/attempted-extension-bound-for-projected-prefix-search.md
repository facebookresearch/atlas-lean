# Attempted-extension bound for projected prefix search

Under the correctness invariant of the prefix algorithm, let $R$ be the number of distinct answers, $h$ the
number of head variables and $A$ the active-domain size. Every layer of retained prefixes has at most $R$
elements, so the algorithm performs at most $1 + hAR$ Boolean tests: the initial test, and at most $A$
attempted extensions of each retained prefix at each of the $h$ depths, failed extensions included. The
term $1$ cannot be dropped: it accounts for the initial test, which is the only test when $R = 0$ or
$h = 0$.

## Expansion

This node states a precise result, an elementary count; it is not a theorem quoted from the cited source.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Algorithm cost model.

## Depends on

- [Projected CQ prefix enumeration and correctness](projected-cq-prefix-enumeration-and-correctness.md)

## Proof depends on

- [Projected CQ prefix enumeration and correctness](projected-cq-prefix-enumeration-and-correctness.md)

## Sources

- Hypertree Decompositions and Tractable Queries (Gottlob, Leone, Scarcello), arXiv cs/9812022v1 manuscript — Authors' arXiv manuscript cs/9812022v1, Section 1.2, item (3) (output-polynomial evaluation of acyclic queries, credited to Yannakakis), as context. <https://arxiv.org/pdf/cs/9812022>
