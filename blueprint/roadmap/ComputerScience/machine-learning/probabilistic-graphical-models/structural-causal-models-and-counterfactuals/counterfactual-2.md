# The single-node counterfactual in a structural causal model with node-wise noise

Let $M$ be a recursive structural causal model on the nodes $0, \dots, n - 1$, listed in a topological order, with values in $\alpha$ and with a noise set $U_k$ of its own at each node $k$: node $k$ has a set $\mathrm{pa}(k)$ of parents among $0, \dots, k - 1$ and a structural function $f_k$ that maps the values of its parents and a noise value $u_k \in U_k$ to a value in $\alpha$. No noise law is part of the model. For a node $k$, a value $a \in \alpha$ and a noise value $u$, the counterfactual
$X_{k \leftarrow a}(u) \in \alpha^n$ is the solution at the same noise value $u$ of the model in
which the structural equation of $k$ is replaced by the constant $a$ and $k$ loses its parents: the
values all nodes would have taken in the unit with noise $u$ had node $k$ been set to $a$.

It intervenes on a single node, while [the unit-level counterfactual](counterfactual.md) of the model
with independent disturbance laws intervenes on a finite set of nodes.
