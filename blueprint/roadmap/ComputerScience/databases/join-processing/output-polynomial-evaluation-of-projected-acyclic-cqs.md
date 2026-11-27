# Output-polynomial evaluation of projected acyclic CQs

Let $Q$ be a safe acyclic conjunctive query with a supplied join tree of size polynomial in $\lVert Q \rVert$, and
$D$ a finite relational instance. The prefix enumerator, which extends retained prefixes of head tuples by
active-domain values and keeps those whose residual Boolean query is nonempty, computes the answer
relation $Q(D)$ in time polynomial in $\lVert Q \rVert + \lVert D \rVert + \lVert Q(D) \rVert$. The bound
combines the call bound of the prefix-search page with a polynomial-time Boolean evaluator for acyclic
queries, and charges filtering, tuple comparison, active-domain operations and output writing
explicitly. It is a sufficient output-polynomial bound; it claims neither time linear in the output nor a
delay bound.

## Expansion

This page becomes ready once a published source states this prefix enumeration, its prefix invariant and its
call count; the cited source gives output-polynomial evaluation of acyclic queries by Yannakakis' method, not this
enumerator.

## Depends on

- [Projected CQ prefix enumeration and correctness](projected-cq-prefix-enumeration-and-correctness.md)
- [Characterizations of acyclic database schemas](characterizations-of-acyclic-database-schemas.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)
- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)

## Proof depends on

- [Projected CQ prefix enumeration and correctness](projected-cq-prefix-enumeration-and-correctness.md)
- [Attempted-extension bound for projected prefix search](attempted-extension-bound-for-projected-prefix-search.md)
- [Yannakakis' algorithm for acyclic join queries](yannakakis-algorithm-for-acyclic-join-queries.md)

## Sources

- Hypertree Decompositions and Tractable Queries (Gottlob, Leone, Scarcello), arXiv cs/9812022v1 manuscript — Authors' arXiv manuscript cs/9812022v1, Section 1.2, item (3) (output-polynomial evaluation of acyclic queries, credited to Yannakakis) and Theorem 4.7, as context; the prefix enumerator is not the source's algorithm. <https://arxiv.org/pdf/cs/9812022>
