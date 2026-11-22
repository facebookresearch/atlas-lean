# Uniqueness of the solution

Let $M$ be a Markovian structural causal model on the nodes $0, \dots, n - 1$ with values in
$\alpha$, disturbances in $\beta$ and structural equations $f_k$. For a disturbance value
$u \in \beta^n$ and an assignment $x \in \alpha^n$, $x$ is the [solution](solve.md) at $u$ if and
only if it satisfies every structural equation at $u$:
$f_k(x_{\mathrm{pa}(k)}, u_k) = x_k$ for all $k$.
