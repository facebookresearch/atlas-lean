# Recursive elastic net for VAR gene networks

Gene networks inferred from time-course expression with a first-order vector autoregressive (VAR) model, where an edge $i \to j$ is a nonzero autoregressive coefficient. Each target gene gives a sparse regression, solved by an elastic net whose $\ell_1$ weights are re-estimated from the previous fit. Reweighting cuts false positive edges while the $\ell_2$ term keeps the grouping of correlated regulators.

- [Recursive elastic net for VAR gene network inference](recursive-elastic-net-for-var-gene-network-inference.md)
- [Grouping-effect bound for the recursive elastic net](grouping-effect-bound-for-the-recursive-elastic-net.md)
