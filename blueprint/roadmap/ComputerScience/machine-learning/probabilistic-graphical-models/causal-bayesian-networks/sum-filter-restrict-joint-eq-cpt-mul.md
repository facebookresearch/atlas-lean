# A node's table is its conditional law given a predecessor set

Let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ with values in a finite nonempty type
$\alpha$ and joint distribution $P$, and write $p_k(\cdot \mid u)$ for the table of node $k$. Let
$Z$ be a finite set of nodes $i < k$ containing the parents of $k$. For every $a \in \alpha$ and
$z \in \alpha^Z$,

$$P(X_k = a, X_Z = z) = p_k(a \mid z_{\mathrm{pa}(k)}) \, P(X_Z = z),$$

where $P(E)$ is the sum of $P(x)$ over the configurations $x \in \alpha^n$ in $E$.
