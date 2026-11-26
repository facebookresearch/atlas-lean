# Extending an environment under a binder

An environment $\rho$ assigns to each variable
index $n \in \mathbb{N}$ a predicate $\rho(n)$ on worlds. Its extension by a predicate $S$ on
worlds is the environment that assigns $S$ to index $0$ and $\rho(n)$ to index $n + 1$.

With de Bruijn indices, variable $1$ inside a binder thus refers to the enclosing binder.
