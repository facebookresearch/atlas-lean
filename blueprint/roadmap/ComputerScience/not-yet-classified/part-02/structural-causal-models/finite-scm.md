# Finite SCM

A finite recursive (acyclic) structural causal model on endogenous nodes `0, …, n - 1`
listed in a topological order, with values in `α` and exogenous noise of type `U k` at node `k`.
Node `k` has parents among the earlier nodes `0, …, k - 1` (the parent convention of
`BayesNet`) and a structural equation `x_k = f_k (x_{pa k}, u_k)`. The exogenous law is not part
of the structure: it is supplied where a probabilistic statement needs it, and independence of
the noises (the Markovian case) is an extra assumption of those statements. Shared or dependent
noise is modelled by explicit latent endogenous nodes.
