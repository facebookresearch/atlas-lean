# Sequences of depth-first search machine steps

Let $G$ be a directed graph with ordered adjacency lists and $R$ a list of roots. A state $t$ of
the depth-first search machine is reached from a state $s$ in zero or more steps when there is a
finite sequence of transitions $s = s_0 \to s_1 \to \dots \to s_k = t$ with $k \ge 0$, each of
which drops a pending vertex that is already visited, discovers a new vertex, or finishes a
vertex: this is the reflexive–transitive closure of the transition relation.
