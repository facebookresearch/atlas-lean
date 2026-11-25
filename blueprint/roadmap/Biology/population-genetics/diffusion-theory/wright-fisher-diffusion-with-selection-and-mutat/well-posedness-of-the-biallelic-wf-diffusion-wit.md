# Well-posedness of the biallelic Wright–Fisher diffusion with general diploid selection and mutation

Let the genotype fitnesses be $1$, $1 + hs$ and $1 + s$, with $c = Ns$ in the convention of [the scale-function ratio with dominance](../selection-duality-and-general-one-dimensional-di/fixation-prob-dominance.md), and let $\theta_1, \theta_2 \ge 0$. The selection drift is

$$b_{\mathrm{sel}}(x) = 2c\, x(1 - x)\bigl(h + (1 - 2h) x\bigr) = x(1 - x)\, V'(x), \qquad V(x) = 2c\Bigl(h x + \frac{(1 - 2h) x^2}{2}\Bigr),$$

with $V$ a quadratic polynomial. The martingale problem for the generator $\mathcal{L}_{0, \theta} + x(1 - x) V'(x) \frac{d}{dx}$ on $[0, 1]$ is well posed:

- **existence:** tilt the [Wright–Fisher diffusion with mutation](../construction-of-the-neutral-wright-fisher-diffus/mutation-wf-transition-kernel-and-canonical-path.md), whose canonical process solves the mutation martingale problem by [the mutation realization](../neutral-wright-fisher-martingale-problem/mutation-realization-solves-the-mutation-marting.md), by $g = e^{V}$, with [the tilted path measure](../construction-of-the-neutral-wright-fisher-diffus/tilted-path-measure-on-a-canonical-space-generic.md) and [the martingale problem under an exponential tilt](../../../../Probability/markov-chains/martingale-problems/martingale-problem-under-exponential-tilt-generi.md). Since

$$\frac{\mathcal{L}_{0, \theta}\, g}{g} = \frac{1}{2} x(1 - x)\bigl(V'' + V'^2\bigr) + \frac{1}{2}\bigl(\theta_1 (1 - x) - \theta_2 x\bigr) V'$$

is bounded, the density process is a martingale, and the tilted generator is exactly the diploid-selection generator;
- **uniqueness:** the inverse tilt and [the well-posedness of the mutation martingale problem](../neutral-wright-fisher-martingale-problem/well-posedness-of-the-mutation-martingale-proble.md).

For $\theta_1, \theta_2 > 0$ the reversible stationary density is proportional to $e^{2V(x)}\, x^{\theta_1 - 1} (1 - x)^{\theta_2 - 1}$.

## Depends on

- [Tilted path measure on a canonical space (generic consistent extension)](../construction-of-the-neutral-wright-fisher-diffus/tilted-path-measure-on-a-canonical-space-generic.md)
- [Martingale problem under exponential tilt (generic)](../../../../Probability/markov-chains/martingale-problems/martingale-problem-under-exponential-tilt-generi.md)
- [Mutation realization solves the mutation martingale problem](../neutral-wright-fisher-martingale-problem/mutation-realization-solves-the-mutation-marting.md)
- [Well-posedness of the Wright–Fisher martingale problem with mutation](../neutral-wright-fisher-martingale-problem/well-posedness-of-the-mutation-martingale-proble.md)
- [Scale-function ratio with dominance](../selection-duality-and-general-one-dimensional-di/fixation-prob-dominance.md)
- [Mutation WF transition kernel and canonical path measure](../construction-of-the-neutral-wright-fisher-diffus/mutation-wf-transition-kernel-and-canonical-path.md)

## Expansion

1. The identity $b_{\mathrm{sel}} = x(1 - x) V'$ and the bound on $\mathcal{L}_{0, \theta} g / g$.
2. Existence by the tilt and uniqueness by the inverse tilt.
3. The stationary density from the speed density for $\theta_1, \theta_2 > 0$.

## Sources

- Y. S. Song and M. Steinrücken, A simple method for finding explicit analytic transition densities of diffusion processes with general diploid selection, *Genetics* 190 (2012), 1117–1129 (general diploid selection).
- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 4, Section 3 (change of measure).
