# A* graph search: consistency, monotone f and reopening

Consider a deterministic search problem with finite branching, step costs at least $\varepsilon > 0$
and a reachable goal, and a heuristic $h \ge 0$ that is admissible ($h \le h^*$, so $h = 0$ at goals),
with the goal test applied when a node is removed from the frontier.

1. If $h$ is consistent ($h(s) \le c(s,a) + h(\mathrm{result}(s,a))$), then $f = g + h$ is nondecreasing
   along every path, A* graph search without reopening expands each state at most once and with its
   optimal path cost, and it returns an optimal solution.
2. If $h$ is only admissible, A* graph search that reopens a closed state whenever a strictly cheaper
   path to it is found returns an optimal solution, while the variant without reopening can return a
   suboptimal one. Example: edges $s_0 \to A$ (cost $1$), $s_0 \to B$ (cost $2$), $A \to C$ (cost $2$),
   $B \to C$ (cost $1/2$), $C \to G$ (cost $3$), goal $G$, and $h(B) = 3$, $h = 0$ elsewhere. This $h$ is
   admissible and inconsistent; without reopening, $C$ is closed with cost $3$ via $A$ before $B$ is
   expanded, and the search returns cost $6$ instead of the optimum $11/2$.

The search model and admissibility are those of the tree-search page.

## Depends on

- [Deterministic search problem](../search-problems-and-uninformed-search/deterministic-search-problem.md)
- [Generic best-first tree/graph search](../search-problems-and-uninformed-search/generic-best-first-tree-graph-search.md)

## Proof depends on

- [A* tree search is optimal under an admissible heuristic](a-tree-search-is-optimal-under-an-admissible-heuristic.md)

## Related topics

- [A\* with a consistent heuristic is optimal](a-star-distance-minimal.md)

## Sources

- P. E. Hart, N. J. Nilsson and B. Raphael, *A formal basis for the heuristic determination of minimum cost paths*, IEEE Transactions on Systems Science and Cybernetics 4(2) (1968) 100–107: algorithm A\* with reopening of closed nodes (Section II-A, step 4, p. 102), Theorem 1 (admissible $\hat h$ gives a minimum-cost path, p. 103), the consistency assumption (5) and Lemma 2 (a closed node already has its optimal cost, so reopening is never needed, p. 104). The counterexample is elementary. <https://ai.stanford.edu/~nilsson/OnlinePubs-Nils/PublishedPapers/astar.pdf>
