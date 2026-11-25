# Existence of the Wright–Fisher diffusion with selection and mutation by an exponential tilt

Let $\alpha \in \mathbb{R}$ and $\theta_1, \theta_2 \ge 0$. Apply [the tilted path measure on a canonical space](../construction-of-the-neutral-wright-fisher-diffus/tilted-path-measure-on-a-canonical-space-generic.md) to the path laws of the [Wright–Fisher diffusion with mutation](../construction-of-the-neutral-wright-fisher-diffus/mutation-wf-transition-kernel-and-canonical-path.md), whose canonical process solves the [martingale problem with mutation](two-way-mutation-and-selection-wright-fisher-mar.md) by [the mutation realization](../neutral-wright-fisher-martingale-problem/mutation-realization-solves-the-mutation-marting.md), with $g(x) = e^{\alpha x}$. Since

$$\frac{\mathcal{L}_{0, \theta}\, g}{g}(x) = \frac{\alpha}{2}\bigl(\theta_1 (1 - x) - \theta_2 x\bigr) + \frac{\alpha^2}{2}\, x (1 - x)$$

is bounded on $[0, 1]$, the [martingale problem under an exponential tilt](../../../../Probability/markov-chains/martingale-problems/martingale-problem-under-exponential-tilt-generi.md) shows that the canonical process under the tilted law $P^g_x$ solves the martingale problem for $\mathcal{L}_{\alpha, \theta}$. The construction uses the mutation realization and the [well-posedness of the mutation martingale problem](../neutral-wright-fisher-martingale-problem/well-posedness-of-the-mutation-martingale-proble.md).

## Depends on

- [Tilted path measure on a canonical space (generic consistent extension)](../construction-of-the-neutral-wright-fisher-diffus/tilted-path-measure-on-a-canonical-space-generic.md)
- [Martingale problem under exponential tilt (generic)](../../../../Probability/markov-chains/martingale-problems/martingale-problem-under-exponential-tilt-generi.md)
- [Mutation WF transition kernel and canonical path measure](../construction-of-the-neutral-wright-fisher-diffus/mutation-wf-transition-kernel-and-canonical-path.md)
- [Mutation realization solves the mutation martingale problem](../neutral-wright-fisher-martingale-problem/mutation-realization-solves-the-mutation-marting.md)
- [Martingale problem for the Wright–Fisher diffusion with selection and two-way mutation](two-way-mutation-and-selection-wright-fisher-mar.md)
- [Well-posedness of the Wright–Fisher martingale problem with mutation](../neutral-wright-fisher-martingale-problem/well-posedness-of-the-mutation-martingale-proble.md)

## Expansion

1. The computation of $\mathcal{L}_{0, \theta} g / g$ and its bound.
2. The application of the generic tilt.
3. A check: $\alpha = 0$ recovers [the mutation realization](../neutral-wright-fisher-martingale-problem/mutation-realization-solves-the-mutation-marting.md).

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 4, Section 3 (exponential change of measure) and Chapter 10.
- S. Wright, Evolution in Mendelian populations, *Genetics* 16 (1931), 97–159, <https://doi.org/10.1093/genetics/16.2.97> (mutation–selection–drift model).
