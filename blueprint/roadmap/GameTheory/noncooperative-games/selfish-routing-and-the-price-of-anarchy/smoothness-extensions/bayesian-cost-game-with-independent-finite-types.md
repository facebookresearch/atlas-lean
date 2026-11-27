# Bayesian cost game with independent finite types

A *Bayesian cost game* has players $i$ with finite type sets $\Theta_i$, independent priors $\pi_i$ on $\Theta_i$, action sets $S_i$, and costs $c_i(\theta; a)$ depending on the full type profile $\theta$ and action profile $a$. A strategy of player $i$ maps types to actions, and a profile $\sigma$ is a *pure Bayes–Nash equilibrium* if for each player $i$ and type $\theta_i$, $\sigma_i(\theta_i)$ minimizes the interim expected cost $\mathbb{E}_{\theta_{-i}}[c_i(\theta; a_i, \sigma_{-i}(\theta_{-i}))]$ over $a_i \in S_i$. The social cost of a type profile and action profile is $\sum_i c_i(\theta; a)$.

## Depends on

- [Bayesian game](../../../not-yet-classified/part-01/bayesian-game/bayesian-game.md)
- [Bayesian Nash equilibrium](../../../not-yet-classified/part-01/bayesian-game/is-bayes-nash.md)

## Sources

- Tim Roughgarden, "The Price of Anarchy in Games of Incomplete Information", Proceedings of the 13th ACM Conference on Electronic Commerce (EC 2012), 2012.
- Vasilis Syrgkanis and Eva Tardos, "Composable and Efficient Mechanisms", Proceedings of the 45th Annual ACM Symposium on Theory of Computing (STOC 2013), 2013.
