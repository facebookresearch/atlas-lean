# Finite recursive structural causal model

A finite recursive structural causal model on endogenous nodes $0, \dots, n-1$, listed in a topological order with values in $\alpha$ and exogenous noise $u_k$ of a given type at node $k$, consists of a parent set for each node $k$ among the earlier nodes $0, \dots, k-1$ and a structural equation $x_k = f_k(x_{\mathrm{pa}(k)}, u_k)$. The exogenous law is not part of the structure, and independence of the noises is not assumed.
