# Sequence-form payoff matrices

For a two-player extensive-form game with perfect recall, the *sequence-form payoff matrix* of player $k$ is the $S_1 \times S_2$ matrix $A_k$ with $A_k(\sigma, \tau) = \sum_z \pi_0(z)\, u_k(z)$, the sum over leaves $z$ whose player-$1$ and player-$2$ sequences are $\sigma$ and $\tau$, weighted by the product $\pi_0(z)$ of chance probabilities. For realization plans $x, y$ the expected payoff of player $k$ is $x^\top A_k y$. The number of nonzero entries of $A_k$ is at most the number of leaves.

## Depends on

- [Sequence form and realization plans](sequence-form-and-realization-plans.md)

## Sources

- Bernhard von Stengel, "Efficient Computation of Behavior Strategies", Games and Economic Behavior, 1996.
- Bernhard von Stengel, "Equilibrium Computation for Two-Player Games in Strategic and Extensive Form", Algorithmic Game Theory, Cambridge University Press, 2007.
