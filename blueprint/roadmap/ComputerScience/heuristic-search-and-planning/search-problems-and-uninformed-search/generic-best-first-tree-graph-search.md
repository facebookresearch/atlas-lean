# Generic best-first tree/graph search

Fix a deterministic search problem and an evaluation function $f$ on search nodes, where a node
records a state, the path that reached it and its path cost $g$. Generic best-first search keeps a
frontier of nodes; at each step it removes a node of minimal $f$ (ties broken by a fixed rule), returns
its path if its state is a goal (goal test on removal), and otherwise inserts the children obtained by
the applicable actions. Tree search keeps no record of visited states. Graph search also keeps a map
from reached states to the least path cost found so far and discards a child whose state was reached
with cost no greater than the child's; the reopening policy states whether a state already removed
from the frontier may be inserted again when a strictly cheaper path is found. An execution with fuel
$N$ performs at most $N$ removals and reports failure, success with a path, or exhaustion of fuel;
termination and optimality are separate theorems under explicit finiteness and cost hypotheses.

## Depends on

- [Deterministic search problem](deterministic-search-problem.md)

## Sources

- P. E. Hart, N. J. Nilsson and B. Raphael, *A formal basis for the heuristic determination of minimum cost paths*, IEEE Transactions on Systems Science and Cybernetics 4(2) (1968) 100–107: the search algorithm A\* of Section II-A (p. 102), a best-first graph search that selects an open node of least $\hat f$, resolves ties by a fixed rule, tests for a goal when a node is selected and reopens closed nodes whose estimate decreases. The scheme above abstracts the evaluation function; the fuel semantics is an editorial convention for executions on infinite state spaces. <https://ai.stanford.edu/~nilsson/OnlinePubs-Nils/PublishedPapers/astar.pdf>
