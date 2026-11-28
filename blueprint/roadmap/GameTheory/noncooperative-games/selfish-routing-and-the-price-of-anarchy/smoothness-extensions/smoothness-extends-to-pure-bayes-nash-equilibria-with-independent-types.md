# Smoothness extends to pure Bayes–Nash equilibria with independent types

Let a Bayesian cost game with independent finite types have social cost $C_\theta(a) = \sum_i c_i(\theta_i; a)$, and let $c^*$ be an optimal choice function: it assigns to every type profile $\theta$ an action profile $c^*(\theta)$ minimizing $C_\theta$, so that $\mathrm{OPT}(\theta) = C_\theta(c^*(\theta))$. Suppose that for some $\lambda > 0$ and $\mu < 1$ the game is $(\lambda, \mu)$-smooth with respect to $c^*$ in Roughgarden's sense:

$$
\sum_i c_i\bigl(\theta_i; (c^*_i(\theta), a_{-i})\bigr) \le \lambda\, C_\theta(c^*(\theta)) + \mu\, C_\varphi(a)
$$

for every type profile $\theta$, every type profile $\varphi$ and every action profile $a$. (The inequality is required for all pairs $\theta, \varphi$, not only for $\varphi = \theta$, which would be smoothness of every induced complete-information game $G_\theta$.) Then every pure Bayes–Nash equilibrium $\sigma$ satisfies

$$
\mathbb{E}_\theta\bigl[C_\theta(\sigma(\theta))\bigr] \le \frac{\lambda}{1 - \mu}\, \mathbb{E}_\theta\bigl[\mathrm{OPT}(\theta)\bigr].
$$

## Proof sketch

Each type $\theta_i$ considers deviating to $c^*_i(\theta_i, \varphi_{-i})$ for a fresh profile $\varphi_{-i}$ of the others' types drawn from the prior. By independence, $(\theta_i, \varphi_{-i})$ is distributed as a type profile and is independent of the others' equilibrium actions $\sigma_{-i}(\theta_{-i})$, so summing the equilibrium conditions and applying the inequality to the type profiles $(\theta_i, \varphi_{-i})$ and $\theta$ with $a = \sigma(\theta)$ gives $\mathbb{E}[C_\theta(\sigma(\theta))] \le \lambda\, \mathbb{E}[\mathrm{OPT}] + \mu\, \mathbb{E}[C_\theta(\sigma(\theta))]$.

## Depends on

- [Bayesian cost game with independent finite types](bayesian-cost-game-with-independent-finite-types.md)
- [Smooth game](../../no-regret-dynamics/is-smooth.md)

## Proof depends on

- [Extension theorem for coarse correlated equilibria](../../no-regret-dynamics/expected-social-cost-le.md)

## Sources

- Tim Roughgarden, "The Price of Anarchy in Games of Incomplete Information", Proceedings of the 13th ACM Conference on Electronic Commerce (EC 2012), 2012.
- Vasilis Syrgkanis and Eva Tardos, "Composable and Efficient Mechanisms", Proceedings of the 45th Annual ACM Symposium on Theory of Computing (STOC 2013), 2013.
