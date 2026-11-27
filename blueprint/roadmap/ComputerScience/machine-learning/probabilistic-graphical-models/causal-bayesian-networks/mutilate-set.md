# Mutilated network of a set intervention

Let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ with values in $\alpha$, $W$ a finite
set of nodes and $w \in \alpha^n$. The network of the intervention $\mathrm{do}(X_W = w_W)$ has the
arrows into $W$ removed: every node $j \in W$ has no parents and the point mass at $w_j$ as its
table, and every other node keeps its parents and its table.
