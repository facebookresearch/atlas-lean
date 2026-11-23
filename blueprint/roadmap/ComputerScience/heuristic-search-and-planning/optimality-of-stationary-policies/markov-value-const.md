# The value of a stationary policy

Let $M$ be a Markov decision process with finitely many states and actions, real rewards and stochastic transitions, and let $0 \le \gamma < 1$. The value of the stationary Markov policy $(\mu, \mu, \dots)$ is the [value of the policy](../value-iteration/policy-value.md) $\mu$, the unique fixed point of $T_\mu$.

## Informally uses

- [N-stage values of a stationary policy](n-stage-value-const.md)
- [A policy's Bellman operator is a contraction](../value-iteration/policy-bellman-contracting.md): the iterates $T_\mu^N 0$ converge to the fixed point of $T_\mu$.
