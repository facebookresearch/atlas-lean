# Fair cost-sharing games are (k, 0)-smooth and have price of anarchy at most k

Every $k$-player fair cost-sharing game with nonnegative resource costs is $(k, 0)$-smooth. Consequently every pure Nash equilibrium and every coarse correlated equilibrium has (expected) total cost at most $k$ times the cost of every profile. The bound is tight: on two parallel links of costs $1 + \varepsilon$ and $k$, all $k$ players on the expensive link form a (strict, for $\varepsilon > 0$) pure Nash equilibrium of cost ratio $k / (1 + \varepsilon)$.

## Proof sketch

A player deviating to its strategy in $s^*$ pays at most the full cost of each resource it uses there, and every resource of $s^*$ is counted at most $k$ times, giving $\sum_i c_i(s^*_i, s_{-i}) \le k\, C(s^*)$.

## Depends on

- [Fair cost-sharing game](../../potential-games/fair-cost-sharing.md)
- [Smooth game](../../no-regret-dynamics/is-smooth.md)

## Proof depends on

- [Extension theorem for coarse correlated equilibria](../../no-regret-dynamics/expected-social-cost-le.md)

## Sources

- Tim Roughgarden, "Intrinsic Robustness of the Price of Anarchy", Journal of the ACM, 2015.
- Eva Tardos and Tom Wexler, "Network Formation Games and the Potential Function Method", Algorithmic Game Theory, Cambridge University Press, 2007.
- Tim Roughgarden and Eva Tardos, "Introduction to the Inefficiency of Equilibria", Algorithmic Game Theory, Cambridge University Press, 2007.
