# Chu-Liu/Edmonds in O(n^3) word-RAM time

There is a deterministic word-RAM program that, given an $n$-vertex digraph with integer arc costs of absolute value at most $M$ as an adjacency and cost matrix and a root $r$, computes a minimum-cost spanning in-arborescence rooted at $r$ (or reports that none exists) within $C (n+1)^3$ instructions, at every word size $w$ with $4(n+1)M + 32(n+1)^2 < 2^w$. The same bound holds for minimum-cost out-arborescences and for maximum-weight branchings.

## Proof sketch

Materialize the adjacency and cost table of each contraction level as an $n \times n$ array with cycle masks and best entry and exit tables; each of at most $n$ levels costs $O(n^2)$ instructions.

## Depends on

- [The Chu-Liu/Edmonds algorithm](chu-liu-edmonds-algorithm.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Correctness and optimality of Chu-Liu/Edmonds](chu-liu-edmonds-correctness.md)
- [Optimum branchings by the super-root reduction](optimum-branching-reduction.md)

## Sources

- R. E. Tarjan, "Finding Optimum Branchings", Networks 7(1), 1977.
- J. Edmonds, "Optimum Branchings", Journal of Research of the National Bureau of Standards, Section B 71B(4), 1967.
