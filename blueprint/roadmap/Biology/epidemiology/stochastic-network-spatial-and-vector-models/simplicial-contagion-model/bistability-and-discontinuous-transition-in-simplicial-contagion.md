# Bistability and discontinuous transition in simplicial contagion

For the simplicial contagion model of order $D = 2$ in mean field, with rescaled infectivities $\lambda = \beta \langle k_1 \rangle / \mu \ge 0$ and $\lambda_\Delta = \beta_\Delta \langle k_2 \rangle / \mu > 0$ and time measured in units of $1/\mu$, the density of infectious vertices obeys

$$\frac{d\rho}{dt} = -\rho + \lambda \rho (1 - \rho) + \lambda_\Delta \rho^2 (1 - \rho) = -\lambda_\Delta \, \rho \, (\rho - \rho^*_{+})(\rho - \rho^*_{-}),$$

where $\rho^*_\pm$ are the roots of $1 - \lambda(1 - \rho) - \lambda_\Delta \rho (1 - \rho) = 0$:

$$\rho^*_{\pm} = \frac{\lambda_\Delta - \lambda \pm \sqrt{(\lambda - \lambda_\Delta)^2 - 4 \lambda_\Delta (1 - \lambda)}}{2 \lambda_\Delta} .$$

**Theorem (phase diagram on $\rho \in [0, 1]$).**

1. If $\lambda_\Delta \le 1$: for $\lambda < 1$ the only admissible steady state is $\rho = 0$, which is stable; for $\lambda > 1$, $\rho = 0$ is unstable and $\rho^*_+ > 0$ is stable. Since $\rho^*_+ \to 0$ as $\lambda \downarrow 1$, the transition at $\lambda = 1$ is continuous, as in the SIS model.
2. If $\lambda_\Delta > 1$, set $\lambda_c = 2\sqrt{\lambda_\Delta} - \lambda_\Delta < 1$.
   - For $\lambda < \lambda_c$ the roots $\rho^*_\pm$ are not real and $\rho = 0$ is the only steady state.
   - For $\lambda_c < \lambda < 1$ one has $0 < \rho^*_- < \rho^*_+$: both $\rho = 0$ and $\rho^*_+$ are stable and $\rho^*_-$ is unstable. Solutions with $\rho(0) < \rho^*_-$ tend to $0$, solutions with $\rho(0) > \rho^*_-$ tend to $\rho^*_+$ (bistability with a critical mass $\rho^*_-$).
   - For $\lambda > 1$, $\rho^*_- < 0 < \rho^*_+$, $\rho = 0$ is unstable and $\rho^*_+$ is the global attractor of $(0, 1]$.

   Because $\rho^*_+ = \rho^*_- = (\lambda_\Delta - \lambda_c)/(2\lambda_\Delta) > 0$ at $\lambda = \lambda_c$, the endemic branch appears with a jump: the transition is discontinuous and shows hysteresis.

## Depends on

- [Simplicial contagion model and its mean-field equation](simplicial-contagion-model-and-its-mean-field-equation.md)

## Expansion

Factor $\rho$ from the right-hand side; the remaining factor is $-(\lambda_\Delta \rho^2 + (\lambda - \lambda_\Delta)\rho + 1 - \lambda)$, whose roots are $\rho^*_\pm$. The discriminant vanishes when $(\lambda + \lambda_\Delta)^2 = 4\lambda_\Delta$, that is at $\lambda = \lambda_c$. The product of the roots is $(1 - \lambda)/\lambda_\Delta$ and their sum is $(\lambda_\Delta - \lambda)/\lambda_\Delta$: for $\lambda < 1$ both roots have the same sign, positive exactly when $\lambda_\Delta > \lambda$, which holds whenever $\lambda_\Delta > 1 > \lambda$; for $\lambda > 1$ they have opposite signs. Stability follows from the sign of the cubic between consecutive roots. When $\lambda_\Delta \le 1$, real roots require $\lambda \ge 2\sqrt{\lambda_\Delta} - \lambda_\Delta \ge \lambda_\Delta$, so their sum is non-positive and, for $\lambda < 1$, both are negative; only $\rho = 0$ remains. The quadratic equals $1 > 0$ at $\rho = 1$, which, together with the root sum $1 - \lambda/\lambda_\Delta < 1$, keeps every admissible root below $1$. Simulations on random simplicial complexes with $\langle k \rangle \approx 20$, $\langle k_\Delta \rangle \approx 6$ reproduce the bistable region and the dependence on the initial density predicted by $\rho^*_-$.

## Sources

- I. Iacopini, G. Petri, A. Barrat and V. Latora, "Simplicial models of social contagion", Nature Communications 10 (2019), Results ("Mean field approach"), Eqs. (2)–(4), <https://doi.org/10.1038/s41467-019-10431-6> (PMC6554271).
- S. Majhi, M. Perc, D. Ghosh, "Dynamics on higher-order networks: a review", Journal of the Royal Society Interface 19 (2022) 20220043, section 4.1 (contagion processes; the same discontinuous transitions, bistability and hysteresis on hypergraphs and temporal higher-order networks), <https://doi.org/10.1098/rsif.2022.0043> (PMC8941407).
