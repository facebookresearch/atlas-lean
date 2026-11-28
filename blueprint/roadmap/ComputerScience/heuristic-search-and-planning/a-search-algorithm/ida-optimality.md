# IDA* optimality

Consider a deterministic search problem with finite branching, positive integer step costs, a solution
of optimal cost $C^*$, and a heuristic $h \ge 0$ that is admissible (so $h = 0$ at goals). IDA* performs
cost-bounded depth-first searches, the first with threshold $h(s_0)$ and each later one with threshold
equal to the least $f = g + h$ value that exceeded the previous threshold. Every threshold is at most
$C^*$, the thresholds strictly increase until a solution is found, and IDA* terminates and returns a
solution of cost $C^*$.

## Depends on

- [Deterministic search problem](../search-problems-and-uninformed-search/deterministic-search-problem.md)

## Proof depends on

- [Iterative deepening depth-first search](../search-problems-and-uninformed-search/iterative-deepening-depth-first-search.md)

## Related topics

- [Consistent heuristic](consistent.md)

## Sources

- R. E. Korf, *Depth-first iterative-deepening: an optimal admissible tree search*, Artificial Intelligence 27 (1985) 97–109, Section 6: IDA\* thresholds (pp. 103–104) and Lemma 6.3 (p. 104), stated there for an admissible monotone cost function. Monotonicity is not needed: every node of an optimal path has $f \le C^*$, so the first node of that path beyond a threshold below $C^*$ bounds the next threshold by $C^*$, and only finitely many nodes have $g \le C^*$. <https://doi.org/10.1016/0004-3702(85)90084-0>
