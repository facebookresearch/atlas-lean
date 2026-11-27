# Parent values in a structural causal model with node-wise noise

Let $M$ be a recursive structural causal model on the nodes $0, \dots, n - 1$, listed in a topological order, with values in $\alpha$ and with a noise set $U_k$ of its own at each node $k$: node $k$ has a set $\mathrm{pa}(k)$ of parents among $0, \dots, k - 1$ and a structural function $f_k$ that maps the values of its parents and a noise value $u_k \in U_k$ to a value in $\alpha$. No noise law is part of the model. For a node $k$ and a full assignment $x \in \alpha^n$, the parent values of $k$ in
$x$ are $(x_j)_{j \in \mathrm{pa}(k)}$.

The [parent values](pa-val.md) of the model with one disturbance set and independent finitely
supported disturbance laws are defined in the same way.
