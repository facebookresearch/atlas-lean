# Under the selection path measure the canonical process solves the selection martingale problem

Let $\alpha \in \mathbb{R}$ and $\theta = 0$, and let $P^\alpha$ be the [selection path measure obtained by an exponential change of measure](../construction-of-the-neutral-wright-fisher-diffus/selection-path-measure-by-exponential-change-of.md) from the neutral law. Under $P^\alpha$ the canonical process solves the [martingale problem for the Wright–Fisher diffusion](../fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md) with selection $\alpha$. This is the special case $L = \mathcal{L}_0$ and $g(x) = e^{\alpha x}$ of [the martingale problem under an exponential tilt](../../../../Probability/markov-chains/martingale-problems/martingale-problem-under-exponential-tilt-generi.md), and it gives existence of a solution for every $\alpha \ne 0$.

## Depends on

- [Selection path measure by exponential change of measure](../construction-of-the-neutral-wright-fisher-diffus/selection-path-measure-by-exponential-change-of.md)
- [Martingale problem under exponential tilt (generic)](../../../../Probability/markov-chains/martingale-problems/martingale-problem-under-exponential-tilt-generi.md)
- [Martingale problem for the Wright–Fisher diffusion](../fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md)

## Expansion

1. The application of the generic tilt with $g = e^{\alpha x}$.
2. Checks: the statement is nonvacuous for $\alpha = 1$, and under $P^\alpha$ the fixation probability from $x$ is the diffusion value $u_\alpha(x)$.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 4, Section 3 and Chapter 10.
- A. Etheridge, *Some Mathematical Models from Population Genetics*, École d'Été de Probabilités de Saint-Flour XXXIX-2009, Lecture Notes in Mathematics 2012 (2011), <https://link.springer.com/book/10.1007/978-3-642-16632-7> (selection via a change of measure).
