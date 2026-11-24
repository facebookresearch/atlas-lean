# Convergence to the stationary law of the Wright–Fisher diffusion with mutation

Let $X$ be the neutral Wright–Fisher diffusion with mutation rates $\theta_1, \theta_2 > 0$, $\theta = \theta_1 + \theta_2$, and no selection, started at any $x \in [0, 1]$. Then the law of $X_t$ converges weakly, as $t \to \infty$, to the Beta$(\theta_1, \theta_2)$ law, whatever $x$.

The [polynomial eigenfunctions](spectral-structure-of-l-0-theta-on-polynomials.md) $R_n$ of the generator decay exactly,

$$\mathbb{E}_x\bigl[R_n(X_t)\bigr] = e^{-\lambda_n t} R_n(x), \qquad \lambda_n = \frac{n(n - 1 + \theta)}{2},$$

while the raw moments are mixtures of these rates,

$$\mathbb{E}_x\bigl[X_t^n\bigr] - \mathbb{E}_\pi\bigl[X^n\bigr] = \sum_{k=1}^{n} c_{n,k}(x)\, e^{-\lambda_k t},$$

with $\pi$ the Beta law, so the slowest rate in every raw moment is $\lambda_1 = \theta/2$, not $\lambda_n$.

## Depends on

- [Polynomial spectrum of the neutral Wright–Fisher generator with mutation](spectral-structure-of-l-0-theta-on-polynomials.md)

## Proof depends on

- [Mutation realization solves the mutation martingale problem](../neutral-wright-fisher-martingale-problem/mutation-realization-solves-the-mutation-marting.md)
- [Compactly supported measures are determined by their moments](../../../../Analysis/harmonic-analysis/integral-transforms/moment-problem-for-compactly-supported-measures/ext-of-forall-integral-pow-eq-of-compl-i.md)
- [Zero probability flux of the Beta density](flux-beta-pdfreal.md)

## Expansion

1. The eigenfunction decay, from the [mutation realization](../neutral-wright-fisher-martingale-problem/mutation-realization-solves-the-mutation-marting.md) and the spectral structure.
2. Convergence of all moments and then weak convergence, since [compactly supported measures are determined by their moments](../../../../Analysis/harmonic-analysis/integral-transforms/moment-problem-for-compactly-supported-measures/ext-of-forall-integral-pow-eq-of-compl-i.md). The Beta law is stationary by [the zero probability flux of the Beta density](flux-beta-pdfreal.md).
3. Checks: $\mathbb{E}_x[X_t] = \theta_1/\theta + (x - \theta_1/\theta)\, e^{-\theta t/2}$. For $\theta_1 = \theta_2 = 1$ and $x = 0$, $\mathbb{E}[X_t^2] - 1/3 = -\frac{1}{2} e^{-t} + \frac{1}{6} e^{-3t}$. The limit does not depend on $x$.

## Sources

- R. C. Griffiths, A transition density expansion for a multi-allele diffusion model, *Adv. Appl. Probab.* 11 (1979), 310–325 (transition density expansion).
- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 10.
