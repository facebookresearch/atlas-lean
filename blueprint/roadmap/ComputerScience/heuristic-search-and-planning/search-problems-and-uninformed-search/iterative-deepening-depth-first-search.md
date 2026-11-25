# Iterative deepening depth-first search

Consider a deterministic search problem in which every state has at most $b \ge 1$ applicable actions,
and suppose a goal exists at minimum depth $d \ge 0$. Iterative deepening runs depth-limited depth-first
tree search with limits $0, 1, 2, \dots$ and goal test on generation of each node, including the root.
It returns a solution with exactly $d$ actions; counting the root as generated once per iteration, the
total number of generated nodes is at most $\sum_{i=0}^{d} (d + 1 - i)\, b^i$, and the search keeps
$O(bd)$ nodes in memory. For $d = 0$ it returns the empty plan after generating only the root.

## Depends on

- [Deterministic search problem](deterministic-search-problem.md)

## Sources

- R. E. Korf, *Depth-first iterative-deepening: an optimal admissible tree search*, Artificial Intelligence 27 (1985) 97–109, Section 4: depth-first iterative-deepening finds a shortest solution, and the proof of Theorem 4.2 counts $b^d + 2b^{d-1} + \dots + d\,b$ generated nodes, roots not counted (pp. 100–101). <https://doi.org/10.1016/0004-3702(85)90084-0>
