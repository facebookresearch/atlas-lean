# Recursion for the truncated moving-average sum

For random variables $(\varepsilon_t)_{t \in \mathbb{Z}}$, a coefficient $\rho$, a time $t$ and $N \in \mathbb{N}$, the truncated moving-average sum $S_N(t) = \sum_{k<N} \rho^k \varepsilon_{t-k}$ satisfies $S_N(t) = \rho\, S_N(t - 1) + \varepsilon_t - \rho^N \varepsilon_{t-N}$: the AR(1) recursion with the dropped tail term as remainder.
