# Greedy breakpoint algorithm for sorting by reversals: further results

Kececioglu and Sankoff (1995) prove, besides the [breakpoint bound for the greedy algorithm](greedy-breakpoint-bound-for-unsigned-sorting-by-reversals.md): (1) the greedy algorithm is a $2$-approximation for the minimum number of reversals sorting an unsigned permutation, because every solution must remove all $\Phi(\pi)$ breakpoints and a reversal removes at most two, so the optimum is at least $\Phi(\pi)/2$, while the greedy algorithm uses at most $\Phi(\pi)$ reversals (their Corollary 1); (2) the greedy algorithm can be implemented in $O(n^2)$ time and $O(n)$ space, by finding the greedy reversal of each of the $O(n)$ iterations in $O(n)$ time (their Section 2.2); and (3) an exact branch-and-bound algorithm, with a lower bound from maximum-weight matchings and linear programming, running in $O(mL(n, n))$ time and $O(n^2)$ space, where $m$ is the size of the search tree and $L(n, n)$ the time to solve a linear program with $n$ variables and $n$ constraints (their Section 3).

## Depends on

- [Greedy breakpoint algorithm for sorting by reversals](greedy-breakpoint-bound-for-unsigned-sorting-by-reversals.md)
- [Unsigned reversal distance of a permutation of 1, …, n](../../../Combinatorics/permutations/permutation-statistics/sorting-by-reversals/udist.md)

## Proof depends on

- [Unsigned breakpoints are at most twice the unsigned reversal distance](../../../Combinatorics/permutations/permutation-statistics/sorting-by-reversals/ub-le-two-mul-udist.md)

## Expansion

1. The lower bound $\mathrm{OPT}(\pi) \ge \Phi(\pi)/2$ in the framed convention of the candidate page, and Corollary 1.
2. The $O(n)$-time search for a greedy reversal and the resulting $O(n^2)$ bound.
3. The matching lower bound of Section 3.1 and its relation with $\Phi(\pi)/2$.
4. The branch-and-bound algorithm of Fig. 7 and its correctness and complexity.

## Sources

- J. Kececioglu and D. Sankoff, Exact and approximation algorithms for sorting by reversals, with application to genome rearrangement, Algorithmica 13 (1995), 180–210. <https://doi.org/10.1007/BF01188586>
