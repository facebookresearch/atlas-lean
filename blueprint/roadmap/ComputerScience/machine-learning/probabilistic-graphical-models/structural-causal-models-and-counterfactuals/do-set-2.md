# Intervention on a set of nodes in a structural causal model with node-wise noise

Let $M$ be a recursive structural causal model on the nodes $0, \dots, n - 1$, listed in a topological order, with values in $\alpha$ and with a noise set $U_k$ of its own at each node $k$: node $k$ has a set $\mathrm{pa}(k)$ of parents among $0, \dots, k - 1$ and a structural function $f_k$ that maps the values of its parents and a noise value $u_k \in U_k$ to a value in $\alpha$. No noise law is part of the model. For a finite set $W$ of nodes and $w \in \alpha^n$, the model after the
intervention $\mathrm{do}(X_W = w)$ gives every node $j \in W$ no parents and the constant structural
function $w_j$, and keeps the parents and structural function of every other node.

It is the [submodel of the intervention](do-set.md) for a model whose nodes have noise sets of their
own and no noise law.
