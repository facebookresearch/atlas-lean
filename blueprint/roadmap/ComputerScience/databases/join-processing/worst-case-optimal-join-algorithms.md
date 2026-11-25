# Worst-case optimal join algorithms (Generic-Join, NPRR, Leapfrog Triejoin)

This node collects the worst-case optimal join algorithms and their running-time bounds, each with its
own input-index and cost conventions.

## Expansion

A sound expansion has separate pages for:

1. **Generic-Join.** For a full join query with a fixed variable order and sorted or trie indexes built in
   advance, the recursion that intersects the candidate values of the next variable across the relevant
   relations, in time proportional to the smallest list, runs in time
   $\tilde O\bigl(\prod_e \lvert R_e \rvert^{x_e} + \sum_e \lvert R_e \rvert\bigr)$ for every fractional edge
   cover $x$, with query-dependent and logarithmic factors as stated in the source; the $\sum_e \lvert R_e \rvert$
   term accounts for building the indexes and is not dominated by the product term, which can be smaller
   than the input.
2. **NPRR.** The algorithm of Ngo, Porat, Ré and Rudra computes the join in time
   $O\bigl(mn \prod_e \lvert R_e \rvert^{x_e} + n^2 \sum_e \lvert R_e \rvert + m^2 n\bigr)$ for every fractional edge cover $x$,
   with $n$ attributes and $m$ relations (Theorem 5.1 and Remark 5.2), assuming joins in time linear in
   input plus output, which holds amortized with hashing or up to a logarithmic factor with sorting.
3. **Leapfrog Triejoin** runs in time $O(Q^* \log n)$ in its trie-iterator model, where $Q^*$ is the
   fractional cover bound and $n$ the largest relation size.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Algorithm cost model.

## Depends on

- [AGM output-size bound for join queries](agm-output-size-bound-for-join-queries.md)
- [Natural join queries, their hypergraphs and fractional edge covers](natural-join-queries-their-hypergraphs-and-fractional-edge-c.md)

## Sources

- Worst-Case Optimal Join Algorithms: Techniques, Results, and Open Problems (Ngo), arXiv:1803.09930v3 — PODS 2018 invited survey, Section 5.1, Algorithm 3 and Theorem 5.1 (backtracking search, cardinality constraints as a special case of acyclic degree constraints). <https://arxiv.org/pdf/1803.09930v3>
- Worst-case Optimal Join Algorithms (Ngo, Porat, Re, Rudra), arXiv:1203.1952 — arXiv (PODS 2012 best paper), Theorem 5.1 and Remark 5.2. <https://arxiv.org/pdf/1203.1952>
- Leapfrog Triejoin: A Simple, Worst-Case Optimal Join Algorithm (Veldhuizen), arXiv:1210.0481v5 — arXiv (ICDT 2014), Abstract and Section 1: leapfrog triejoin runs in $O(Q^* \log n)$ time. <https://arxiv.org/html/1210.0481v5>
