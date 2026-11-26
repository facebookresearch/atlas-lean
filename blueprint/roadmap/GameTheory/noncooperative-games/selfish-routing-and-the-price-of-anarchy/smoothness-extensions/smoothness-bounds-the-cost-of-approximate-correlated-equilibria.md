# Smoothness bounds the cost of approximate correlated equilibria

Let $G$ be $(\lambda, \mu)$-smooth with $\mu < 1$ and nonnegative social cost. If $\sigma$ is an approximate correlated equilibrium in which player $i$ gains at most $\varepsilon_i$ from any switching function, then for every profile $s^*$,

$$
\mathbb{E}_{s \sim \sigma}[C(s)] \le \frac{\lambda\, C(s^*) + \sum_i \varepsilon_i}{1 - \mu}.
$$

In particular mixed Nash equilibria and exact correlated equilibria cost at most $\frac{\lambda}{1-\mu} C(s^*)$.

## Proof sketch

Apply the approximate equilibrium condition with the constant switching function $a \mapsto s^*_i$, sum over players and use smoothness inside the expectation.

## Depends on

- [Smooth game](../../no-regret-dynamics/is-smooth.md)
- [Correlated equilibrium](../../correlated-equilibria/is-correlated-eq.md)

## Proof depends on

- [Extension theorem for coarse correlated equilibria](../../no-regret-dynamics/expected-social-cost-le.md)

## Sources

- Tim Roughgarden, "Intrinsic Robustness of the Price of Anarchy", Journal of the ACM, 2015.
