# The intervention $\mathrm{do}(X_k = a)$

Let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ with values in $\alpha$, let $k$ be a
node and $a \in \alpha$. The network of the intervention $\mathrm{do}(X_k = a)$ replaces the
mechanism of node $k$ by the point mass at $a$ and deletes all incoming arrows to $k$ (its parent
set becomes empty); every other node keeps its parents and its table.
