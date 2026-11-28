# Iacono's unified bound

For an access sequence $X = (x_1, \dots, x_m)$ on $[n]$, and times $t' < t$, let $w(t', t)$ be the number of distinct keys accessed at times in $(t', t)$. The *unified bound* is $\mathrm{UB}(X) = \sum_{t=1}^m \min_{t' < t} \log_2\big(w(t', t) + |x_{t'} - x_t| + 2\big)$, where for $t = 1$ the minimum is replaced by $\log_2 (n + 2)$. A key accessed recently or close in key space to a recently accessed key is cheap.

## Depends on

- [The binary search tree access model](../dynamic-optimality/the-binary-search-tree-access-model.md)

## Sources

- John Iacono, "Alternatives to Splay Trees with O(log n) Worst-Case Access Times", SODA (2001).
- Mihai Bădoiu, Richard Cole, Erik D. Demaine, John Iacono, "A Unified Access Bound on Comparison-Based Dynamic Dictionaries", Theoretical Computer Science 382(2) (2007).
