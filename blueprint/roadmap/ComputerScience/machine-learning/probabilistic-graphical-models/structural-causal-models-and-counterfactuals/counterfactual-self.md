# Effectiveness of the single-node counterfactual

Let $M$ be a recursive structural causal model on the nodes $0, \dots, n - 1$, listed in a topological order, with values in $\alpha$ and with a noise set $U_k$ of its own at each node $k$: node $k$ has a set $\mathrm{pa}(k)$ of parents among $0, \dots, k - 1$ and a structural function $f_k$ that maps the values of its parents and a noise value $u_k \in U_k$ to a value in $\alpha$. No noise law is part of the model. For every node $k$, value $a \in \alpha$ and noise value $u$, the counterfactual in
which $k$ is set to $a$ gives $k$ the value $a$: $X_{k \leftarrow a}(u)_k = a$.

This is the single-node case, for a model with node-wise noise sets, of
[effectiveness](counterfactual-of-mem.md).
