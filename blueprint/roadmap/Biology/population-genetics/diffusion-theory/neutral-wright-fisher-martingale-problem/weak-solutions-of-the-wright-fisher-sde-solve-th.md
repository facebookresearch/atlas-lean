# Weak solutions of the Wright–Fisher SDE solve the Wright–Fisher martingale problem

Let $\alpha \in \mathbb{R}$ and $\theta_1, \theta_2 \ge 0$, and let $X$ be a $[0, 1]$-valued weak solution, with continuous paths, of the stochastic differential equation

$$dX_t = b(X_t)\, dt + \sigma(X_t)\, dW_t, \qquad b(x) = \alpha x (1 - x) + \tfrac{1}{2}\bigl(\theta_1 (1 - x) - \theta_2 x\bigr), \quad \sigma(x) = \sqrt{x(1 - x)}.$$

Then $X$ solves the [martingale problem for the Wright–Fisher diffusion with selection and two-way mutation](../wright-fisher-diffusion-with-mutation/two-way-mutation-and-selection-wright-fisher-mar.md), with test functions in $C^2[0, 1]$ extended to $C^2_b(\mathbb{R})$. This is the special case $E = [0, 1]$ of [strong solutions solve the martingale problem](../../../../Probability/markov-chains/martingale-problems/strong-solutions-solve-the-martingale-problem.md), branch (i): the operator $A f = b f' + \frac{1}{2} x(1 - x) f''$ is $\mathcal{L}_{\alpha, \theta} f$, and the local martingales are true martingales because $E$ is compact.

## Depends on

- [Strong solutions solve the martingale problem](../../../../Probability/markov-chains/martingale-problems/strong-solutions-solve-the-martingale-problem.md)
- [Martingale problem for the Wright–Fisher diffusion with selection and two-way mutation](../wright-fisher-diffusion-with-mutation/two-way-mutation-and-selection-wright-fisher-mar.md)

## Expansion

1. The coefficient check: $A f$ from [the general result](../../../../Probability/markov-chains/martingale-problems/strong-solutions-solve-the-martingale-problem.md) equals $\mathcal{L}_{\alpha, \theta} f$ on $[0, 1]$.
2. The extension of test functions from $C^2[0, 1]$ to $C^2_b(\mathbb{R})$, which does not change $A f$ on $[0, 1]$.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 5, Section 3 (stochastic equations and martingale problems).
- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer (1991), <https://doi.org/10.1007/978-1-4612-0949-2>, Chapter 5 (weak solutions).
- D. W. Stroock and S. R. S. Varadhan, *Multidimensional Diffusion Processes*, Springer (1979) (martingale problems).
