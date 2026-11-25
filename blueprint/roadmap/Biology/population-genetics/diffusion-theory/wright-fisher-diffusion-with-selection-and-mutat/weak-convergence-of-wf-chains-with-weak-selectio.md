# Weak convergence of Wright–Fisher chains with weak selection and mutation

Fix $\alpha \in \mathbb{R}$, $\theta_1, \theta_2 \ge 0$ and $T > 0$. Let $X^M$ be the Wright–Fisher chains on $M$ gene copies with $s = \alpha / M$ and $u_i = \theta_i / (2M)$ (for all $M > \max(\lvert\alpha\rvert, \theta_1/2, \theta_2/2)$, so that $0 \le u_i \le 1$ and $s > -1$ and the transition below is well defined), run at time scale $M$, with $X^M_0 \Rightarrow \mu$. Then $X^M$ converges in distribution in $D([0, T], [0, 1])$, to a continuous limit, the unique solution of the martingale problem for $(\mathcal{L}_{\alpha, \theta}, \mu)$.

The proof assembles, by [the diffusion-approximation framework](../../../../Probability/markov-chains/martingale-problems/diffusion-approximation-framework-process-level.md), the identification of the [limit points](limit-points-of-wf-chains-solve-the-l-alpha-thet.md), through [existence by approximation](../../../../Probability/markov-chains/martingale-problems/existence-by-approximation-limits-of-chains-solv.md), and the [uniqueness under the inverse tilt](../wright-fisher-diffusion-with-mutation/uniqueness-for-the-selection-mutation-martingale.md).

## Depends on

- [Limit points of Wright–Fisher chains solve the martingale problem with selection and mutation](limit-points-of-wf-chains-solve-the-l-alpha-thet.md)
- [Existence by approximation: limits of chains solve the limit martingale problem](../../../../Probability/markov-chains/martingale-problems/existence-by-approximation-limits-of-chains-solv.md)
- [Diffusion-approximation framework (process-level convergence)](../../../../Probability/markov-chains/martingale-problems/diffusion-approximation-framework-process-level.md)
- [Uniqueness for the selection–mutation martingale problem by an inverse tilt](../wright-fisher-diffusion-with-mutation/uniqueness-for-the-selection-mutation-martingale.md)

## Expansion

1. The assembly from the pages cited.
2. The tightness bound, uniform in $(\alpha, \theta)$ on compact sets.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 10, Sections 1 and 2, and Chapter 4, Section 8.
- S. N. Ethier and T. Nagylaki, Diffusion approximations of Markov chains with two time scales and applications to population genetics, *Adv. Appl. Probab.* 12 (1980), 14–49.
