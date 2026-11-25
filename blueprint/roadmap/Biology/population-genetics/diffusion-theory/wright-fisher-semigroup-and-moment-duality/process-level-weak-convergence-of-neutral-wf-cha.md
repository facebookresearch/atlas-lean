# Process-level weak convergence of neutral Wright–Fisher chains to the diffusion

Let $X^{(M)}$ be the neutral Wright–Fisher frequency chain on $M$ gene copies started at $x_M \to x$, and $Y^M$ the piecewise-linear interpolation of $t \mapsto X^{(M)}_{\lfloor tM \rfloor}$ on $[0, T]$. Then the laws of $Y^M$ on $C([0, T])$ converge weakly to the law of the neutral Wright–Fisher diffusion started at $x$.

This is convergence of the processes, stronger than [the generator form of the diffusion limit](../diffusion-limit-of-the-wright-fisher-model/tendsto-wf-generator.md) and than [the finite-dimensional convergence](finite-dimensional-convergence-of-rescaled-wf-ch.md).

## Depends on

- [Finite-dimensional convergence of rescaled neutral Wright–Fisher chains](finite-dimensional-convergence-of-rescaled-wf-ch.md)
- [Tightness of interpolated rescaled Wright–Fisher chains in C([0,T])](tightness-of-interpolated-rescaled-wf-chains-in.md)

## Proof depends on

- [Continuous modification selected by Kolmogorov's theorem](../construction-of-the-neutral-wright-fisher-diffus/continuous-realization-2.md)
- [Diffusion-approximation framework (process-level convergence)](../../../../Probability/markov-chains/martingale-problems/diffusion-approximation-framework-process-level.md)

## Expansion

1. Finite-dimensional convergence and tightness give convergence in $C([0, T])$, with the limit identified through [the continuous realization](../construction-of-the-neutral-wright-fisher-diffus/continuous-realization-2.md) and [the diffusion-approximation framework](../../../../Probability/markov-chains/martingale-problems/diffusion-approximation-framework-process-level.md).
2. A corollary by continuous mapping: the law of $\max_{t \le T} Y^M(t)$ converges.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 10, Theorem 1.1.
- W. Feller, Diffusion processes in genetics, in *Proc. Second Berkeley Symp. Math. Statist. Probab.*, University of California Press (1951), 227–246, <http://digitalassets.lib.berkeley.edu/math/ucb/text/math_s2_article-17.pdf> (diffusion approximation).
