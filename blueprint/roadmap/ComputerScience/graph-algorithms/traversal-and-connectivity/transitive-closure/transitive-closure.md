# Saved-matrix transitive-closure algorithm

Given a Boolean adjacency matrix $A$ on the
vertices $0, 1, \dots, n-1$, the algorithm first builds the matrix $t^{(0)}$ with $t^{(0)}_{ij}$
true exactly when $i = j$ or $A_{ij}$ is true. Then, for $k = 0, 1, \dots, n-1$ in turn, it
builds a new matrix $t^{(k+1)}$ with
$t^{(k+1)}_{ij} = t^{(k)}_{ij} \lor (t^{(k)}_{ik} \land t^{(k)}_{kj})$ for all $i, j$, reading
every operand from the saved matrix $t^{(k)}$, and it returns $t^{(n)}$. One time unit is
charged for each cell assignment; reads, Boolean operations and matrix allocation are free.

This is the saved-matrix recurrence of CLRS for the reflexive transitive closure.
