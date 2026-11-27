# A node's table is its conditional law given its parents

Let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ with values in a finite nonempty type
$\alpha$ and joint distribution $P$, and write $p_k(\cdot \mid z)$ for the table of node $k$. For
every node $k$, $a \in \alpha$ and values $z$ of the parents of $k$,

$$P(X_k = a, X_{\mathrm{pa}(k)} = z) = p_k(a \mid z) \, P(X_{\mathrm{pa}(k)} = z),$$

where $P(E)$ is the sum of $P(x)$ over the configurations $x \in \alpha^n$ in $E$.
