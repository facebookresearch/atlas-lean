# Smoothness extends to pure Bayes–Nash equilibria with independent types

Let a Bayesian cost game with independent finite types be such that, for every type profile $\theta$, the complete-information game $G_\theta$ is $(\lambda, \mu)$-smooth with $\mu < 1$, where in the smoothness inequality the deviation of player $i$ depends only on $\theta$ through $\theta_i$ and on the benchmark optimal strategies. Then every pure Bayes–Nash equilibrium $\sigma$ satisfies

$$
\mathbb{E}_\theta\bigl[C_\theta(\sigma(\theta))\bigr] \le \frac{\lambda}{1 - \mu}\, \mathbb{E}_\theta\bigl[\mathrm{OPT}(\theta)\bigr].
$$

## Proof sketch

Each type $\theta_i$ considers deviating to the action it would play in the optimal outcome of a fresh type profile drawn independently for the others; independence of types lets the equilibrium condition be averaged against this deviation, and the smoothness inequality applied pointwise gives the bound.

## Depends on

- [Bayesian cost game with independent finite types](bayesian-cost-game-with-independent-finite-types.md)
- [Smooth game](../../no-regret-dynamics/is-smooth.md)

## Proof depends on

- [Extension theorem for coarse correlated equilibria](../../no-regret-dynamics/expected-social-cost-le.md)

## Sources

- Tim Roughgarden, "The Price of Anarchy in Games of Incomplete Information", Proceedings of the 13th ACM Conference on Electronic Commerce (EC 2012), 2012.
- Vasilis Syrgkanis and Eva Tardos, "Composable and Efficient Mechanisms", Proceedings of the 45th Annual ACM Symposium on Theory of Computing (STOC 2013), 2013.
