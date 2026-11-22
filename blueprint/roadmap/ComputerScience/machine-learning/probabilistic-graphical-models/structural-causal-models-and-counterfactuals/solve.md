# Solution of the structural equations

Let $M$ be a Markovian structural causal model on the nodes $0, \dots, n - 1$ with values in
$\alpha$, disturbances in $\beta$ and structural equations $f_k$. The solution at a disturbance
value $u \in \beta^n$ is the assignment $X(u) \in \alpha^n$ computed node by node along the
topological order: $X(u)_k = f_k\big((X(u)_j)_{j \in \mathrm{pa}(k)}, u_k\big)$.

## Related topics

- [Solution of a structural causal model with node-wise noise](solve-2.md): the same solution for a model whose nodes have noise sets of their own and no noise law.
