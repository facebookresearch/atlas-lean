# Deterministic search problem

A deterministic search problem consists of a set $S$ of states, an initial state $s_0$, for each state $s$
a set $\mathrm{Act}(s)$ of applicable actions, a transition function giving the state
$\mathrm{result}(s, a)$ for $a \in \mathrm{Act}(s)$, a decidable goal predicate and step costs
$c(s, a) \ge 0$. A solution from $s$ is a finite sequence of applicable actions whose induced path ends
in a goal state; its cost is the sum of its step costs; $h^*(s) \in [0, \infty]$ is the infimum of the
costs of solutions from $s$, and $\infty$ when there is none. The problem is finitely branching if every
$\mathrm{Act}(s)$ is finite; this does not require $S$ to be finite.

## Sources

- P. E. Hart, N. J. Nilsson and B. Raphael, *A formal basis for the heuristic determination of minimum cost paths*, IEEE Transactions on Systems Science and Cybernetics 4(2) (1968) 100–107, Section I-B (pp. 100–101): graphs given implicitly by a start node and a successor operator returning successors with arc costs, paths and their costs, goal sets, and $h(n)$, the cost of an optimal path from $n$ to a goal. Actions here label the arcs. <https://ai.stanford.edu/~nilsson/OnlinePubs-Nils/PublishedPapers/astar.pdf>
