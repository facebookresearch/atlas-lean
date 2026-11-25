# A* tree search is optimal under an admissible heuristic

Consider a deterministic search problem with finite branching, step costs at least $\varepsilon > 0$,
and a solution of optimal cost $C^*$. Let $h \ge 0$ be admissible ($h \le h^*$; then $h = 0$ at goals).
A* tree search, which keeps no duplicate detection, orders the frontier by $f = g + h$ and applies the
goal test when a node is removed from the frontier, terminates and returns a solution of cost $C^*$;
every node it expands has $f \le C^*$, and only finitely many nodes have $g \le C^*$. Nonnegativity of
$h$ is part of the hypothesis; the solution-cost guarantee is a separate statement from bounds on the
number of expanded nodes.

## Depends on

- [Deterministic search problem](../search-problems-and-uninformed-search/deterministic-search-problem.md)
- [Generic best-first tree/graph search](../search-problems-and-uninformed-search/generic-best-first-tree-graph-search.md)

## Related topics

- [A\* with a consistent heuristic is optimal](a-star-distance-minimal.md)

## Sources

- P. E. Hart, N. J. Nilsson and B. Raphael, *A formal basis for the heuristic determination of minimum cost paths*, IEEE Transactions on Systems Science and Cybernetics 4(2) (1968) 100–107: Lemma 1, its corollary and Theorem 1 (pp. 102–103), for graphs whose arc costs are at least $\delta > 0$; tree search is A\* on the search tree, where no state is reached twice. <https://ai.stanford.edu/~nilsson/OnlinePubs-Nils/PublishedPapers/astar.pdf>
