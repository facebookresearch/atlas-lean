# Solution of a structural causal model with node-wise noise

Let $M$ be a recursive structural causal model on the nodes $0, \dots, n - 1$, listed in a topological order, with values in $\alpha$ and with a noise set $U_k$ of its own at each node $k$: node $k$ has a set $\mathrm{pa}(k)$ of parents among $0, \dots, k - 1$ and a structural function $f_k$ that maps the values of its parents and a noise value $u_k \in U_k$ to a value in $\alpha$. No noise law is part of the model. At a noise value $u = (u_k)_k$, the solution is the assignment $X(u) \in \alpha^n$
computed node by node in the topological order: $X(u)_k = f_k\bigl((X(u)_j)_{j \in \mathrm{pa}(k)}, u_k\bigr)$.

It is the [solution of the structural equations](solve.md) for a model whose nodes have noise sets
of their own and no noise law.
