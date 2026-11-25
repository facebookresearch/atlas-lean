# Limit points of Wright–Fisher chains solve the martingale problem with selection and mutation

Fix $\alpha \in \mathbb{R}$, $\theta_1, \theta_2 \ge 0$ and $T > 0$, and let $X^M$ be the Wright–Fisher chains on $M$ gene copies with $s = \alpha / M$ and $u_i = \theta_i / (2M)$ (for all $M > \max(\lvert\alpha\rvert, \theta_1/2, \theta_2/2)$, so that $0 \le u_i \le 1$ and $s > -1$ and the transition below is well defined), run at time scale $M$, with initial laws converging, $X^M_0 \Rightarrow \mu$. Then every subsequential limit in distribution of $X^M$ in $D([0, T], [0, 1])$ solves the martingale problem for $(\mathcal{L}_{\alpha, \theta}, \mu)$.

This is the special case $E = [0, 1]$ of [existence by approximation](../../../../Probability/markov-chains/martingale-problems/existence-by-approximation-limits-of-chains-solv.md), with

- the countable core of [polynomials with rational coefficients](countable-polynomial-graph-core-for-l-alpha-thet.md);
- the [uniform convergence of the generators](../wright-fisher-diffusion-with-mutation/uniform-generator-convergence-with-selection-and.md), $\sup_x \lvert A_M p - \mathcal{L}_{\alpha, \theta}\, p \rvert \to 0$ for each core polynomial $p$, which is of class $C^3$;
- the [C-tightness of the rescaled chains](../wright-fisher-diffusion-with-mutation/c-tightness-of-rescaled-wf-chains-with-selection.md);
- the convergence of the initial laws, an explicit hypothesis.

## Depends on

- [Existence by approximation: limits of chains solve the limit martingale problem](../../../../Probability/markov-chains/martingale-problems/existence-by-approximation-limits-of-chains-solv.md)
- [A countable polynomial core for the Wright–Fisher generator with selection and mutation](countable-polynomial-graph-core-for-l-alpha-thet.md)
- [Uniform generator convergence of the Wright–Fisher chain with selection and mutation](../wright-fisher-diffusion-with-mutation/uniform-generator-convergence-with-selection-and.md)
- [C-tightness of rescaled Wright–Fisher chains with selection and mutation](../wright-fisher-diffusion-with-mutation/c-tightness-of-rescaled-wf-chains-with-selection.md)

## Expansion

The statement follows from the general theorem once its four hypotheses are checked from the pages cited.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 4, Section 8 (convergence via martingale problems).
