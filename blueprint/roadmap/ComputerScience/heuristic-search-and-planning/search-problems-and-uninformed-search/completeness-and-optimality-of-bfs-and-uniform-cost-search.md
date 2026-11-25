# Completeness and optimality of BFS and uniform-cost search

Consider a deterministic search problem with finite branching in which some goal is reachable.

1. **Breadth-first search.** Let $d$ be the minimum number of actions of a solution. Breadth-first tree
   search (FIFO frontier, goal test on removal) returns a solution with exactly $d$ actions, after
   removing at most the number of nodes of depth at most $d$ from the frontier; in particular it
   succeeds with any fuel larger than that number.
2. **Uniform-cost search.** If every step cost is at least $\varepsilon > 0$ (for example natural numbers
   at least $1$), uniform-cost search ($f = g$, goal test on removal) returns a solution of minimum
   cost. The hypothesis matters: with zero-cost cycles or infinitely many applicable actions the search
   can fail to terminate or to return an optimal solution.

## Depends on

- [Deterministic search problem](deterministic-search-problem.md)
- [Generic best-first tree/graph search](generic-best-first-tree-graph-search.md)

## Sources

- R. E. Korf, *Depth-first iterative-deepening: an optimal admissible tree search*, Artificial Intelligence 27 (1985) 97–109, Section 2 (breadth-first search finds a shortest solution, pp. 98–99). <https://doi.org/10.1016/0004-3702(85)90084-0>
- P. E. Hart, N. J. Nilsson and B. Raphael, *A formal basis for the heuristic determination of minimum cost paths*, IEEE Transactions on Systems Science and Cybernetics 4(2) (1968) 100–107, Theorem 1 (p. 103) with the estimate $\hat h = 0$, which is consistent, so that A\* is uniform-cost search; arc costs at least $\delta > 0$. <https://ai.stanford.edu/~nilsson/OnlinePubs-Nils/PublishedPapers/astar.pdf>
