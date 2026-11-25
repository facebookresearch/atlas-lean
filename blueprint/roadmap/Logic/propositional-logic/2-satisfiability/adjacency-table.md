# Adjacency table of the implication graph

For a CNF formula $\varphi$, the hash map that
sends each literal over the variables of $\varphi$ to the list of its implication-graph
successors, that is, of the literals $m$ over the variables of $\varphi$ with an implication edge
from it to $m$.

The table is computed once so that the SCC traversal looks successor lists up in expected
constant time.
