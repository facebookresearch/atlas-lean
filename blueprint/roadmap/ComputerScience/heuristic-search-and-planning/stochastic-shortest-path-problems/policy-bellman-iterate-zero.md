# The N-stage total reward

For a Markov decision process with finitely many states, a deterministic stationary policy $\mu$ and every $N \ge 0$,

$$T_\mu^N 0 = \sum_{k=0}^{N-1} P_\mu^k r_\mu,$$

the expected total reward of the first $N$ stages (in a stochastic shortest path problem, rewards stop at termination, which the substochastic matrix $P_\mu$ accounts for).

## Informally uses

- [Undiscounted Bellman operators are affine](policy-bellman-one-eq.md)
