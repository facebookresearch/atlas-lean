# Feller semigroup and transition kernels of the Wright–Fisher diffusion with selection

Let $\alpha \in \mathbb{R}$, with no mutation ($\theta = 0$), and let $P^\alpha_x$ be the law of the Wright–Fisher diffusion with genic selection $\alpha$ started at $x$, obtained from the neutral law $P^0_x$ by the change of measure with density process $Z^\alpha$ of [the uniqueness for the selection martingale problem](../wright-fisher-diffusion-with-selection-and-mutat/uniqueness-for-the-selection-martingale-problem.md). Let $\kappa^\alpha_t(x, \cdot)$ be the law of $X_t$ under $P^\alpha_x$. Then:

1. $(\kappa^\alpha_t)_{t \ge 0}$ is a family of Markov kernels satisfying the Chapman–Kolmogorov equations;
2. the semigroup $P^\alpha_t f(x) = \mathbb{E}^0_x\bigl[Z^\alpha_t\, f(X_t)\bigr]$ has the Feller property: $x \mapsto P^\alpha_t f(x)$ is continuous for $f \in C[0, 1]$;
3. the canonical process under $P^\alpha_x$ is Markov with transition kernels $\kappa^\alpha$.

## Depends on

- [Uniqueness for the selection martingale problem by an inverse change of measure](../wright-fisher-diffusion-with-selection-and-mutat/uniqueness-for-the-selection-martingale-problem.md)

## Proof depends on

- [Strong Markov property of the neutral Wright–Fisher diffusion](../strong-markov-property-of-the-wright-fisher-diff/cond-exp-stopped-value-add-ae-eq.md)

## Expansion

1. The Feller continuity of $x \mapsto P^\alpha_t f(x)$, from the continuity in $x$ of the neutral path law.
2. The Chapman–Kolmogorov equations and the Markov property, from the [strong Markov property of the neutral diffusion](../strong-markov-property-of-the-wright-fisher-diff/cond-exp-stopped-value-add-ae-eq.md) and the multiplicativity of $Z^\alpha$.
3. A check: $\alpha = 0$ recovers the neutral kernels.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 4, Theorem 4.2 (a well-posed martingale problem gives a Markov process).
