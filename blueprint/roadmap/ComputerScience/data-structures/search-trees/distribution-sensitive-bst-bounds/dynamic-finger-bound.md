# Dynamic finger bound

The *dynamic finger bound* of an access sequence $X = (x_1, \dots, x_m)$ on $[n]$ is $\mathrm{DF}(X) = \sum_{t=2}^m \log_2(|x_t - x_{t-1}| + 2)$, the cost of searching from the previously accessed key with an exponential search. The *working-set bound* is $\mathrm{WS}(X) = \sum_{t=1}^m \log_2(\omega_t + 2)$, where $\omega_t$ is the number of distinct keys accessed since the previous access to $x_t$ (or $n$ if there is none).

## Depends on

- [The binary search tree access model](../dynamic-optimality/the-binary-search-tree-access-model.md)

## Sources

- Richard Cole, "On the Dynamic Finger Conjecture for Splay Trees. Part II: The Proof", SIAM Journal on Computing 30(1) (2000).
- Daniel D. Sleator, Robert E. Tarjan, "Self-Adjusting Binary Search Trees", Journal of the ACM 32(3) (1985).
