# Deterministic search problem

A deterministic search problem on a type $S$ of states consists of an initial state $s_0 \in S$; for each state $s$, a
type $\mathrm{Act}(s)$ of the actions applicable at $s$; for each $a \in \mathrm{Act}(s)$, a successor state
$\mathrm{result}(s, a) \in S$; a decidable goal predicate on $S$; and for each $a \in \mathrm{Act}(s)$, a finite
nonnegative step cost $c(s, a) \in [0, \infty)$. Neither $S$ nor the action types need be finite, and applicability
need not be decidable.

Solutions from a state, their costs, the optimal cost $h^*(s)$ and finite branching are defined from these data.

## Sources

- P. E. Hart, N. J. Nilsson and B. Raphael, *A formal basis for the heuristic determination of minimum cost paths*, IEEE Transactions on Systems Science and Cybernetics 4(2) (1968) 100–107, Section I-B (pp. 100–101): graphs given implicitly by a start node and a successor operator returning successors with arc costs, paths and their costs, goal sets, and $h(n)$, the cost of an optimal path from $n$ to a goal. Actions here label the arcs. <https://ai.stanford.edu/~nilsson/OnlinePubs-Nils/PublishedPapers/astar.pdf>
