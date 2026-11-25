# Consistency of the single-node counterfactual

Let $M$ be a recursive structural causal model on the nodes $0, \dots, n - 1$, listed in a topological order, with values in $\alpha$ and with a noise set $U_k$ of its own at each node $k$: node $k$ has a set $\mathrm{pa}(k)$ of parents among $0, \dots, k - 1$ and a structural function $f_k$ that maps the values of its parents and a noise value $u_k \in U_k$ to a value in $\alpha$. No noise law is part of the model. If node $k$ already takes the value $a$ in the unit with noise value $u$, that is
$X(u)_k = a$, then setting $k$ to $a$ changes nothing: $X_{k \leftarrow a}(u) = X(u)$.

This is the single-node case, for a model with node-wise noise sets, of
[consistency](counterfactual-eq-solve.md).
