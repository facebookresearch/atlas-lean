# The solution satisfies the structural equations

Let $M$ be a Markovian structural causal model on the nodes $0, \dots, n - 1$ with values in
$\alpha$, disturbances in $\beta$ and structural equations $f_k$. For every $u \in \beta^n$ and
every node $k$, the [solution](solve.md) satisfies $X(u)_k = f_k(X(u)_{\mathrm{pa}(k)}, u_k)$.
