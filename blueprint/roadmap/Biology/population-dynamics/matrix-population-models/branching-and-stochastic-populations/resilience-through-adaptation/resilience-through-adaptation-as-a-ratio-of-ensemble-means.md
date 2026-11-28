# Resilience through adaptation as a ratio of ensemble means

**Setting.** A noisy system $X$ (a Markov process with generator $\mathcal L_{e,\theta}$ depending on environmental parameters $e$ and physiological parameters $\theta$) starts in its invariant distribution $\bar p_{e_0,\theta_0}$. At time $0$ the environment changes $e_0 \to e_1$; at an independent random reaction time $\tau \sim \mathrm{Exp}(\lambda)$ the system adapts $\theta_0 \to \theta_1$. A success function $S$ measures performance; $\bar S_{e,\theta}$ is its mean under $\bar p_{e,\theta}$, so $\mathbb E S(X(0)) = \bar S_{e_0,\theta_0}$ and $\mathbb E S(X(t)) \to \bar S_{e_1,\theta_1}$.

**Definition.** With $\bar S^\tau_{e_1,\theta_0} = \mathbb E\, S(X(\tau))$, the success at the moment of adaptation, the *resilience through adaptation* is

$$R_\tau = \frac{\bar S_{e_1,\theta_1} - \bar S^\tau_{e_1,\theta_0}}{\bar S_{e_0,\theta_0} - \bar S^\tau_{e_1,\theta_0}} .$$

**Properties.**
1. $R_\tau$ depends only on ensemble averages. Since $\tau$ is exponential and independent of the paths of the pre-adaptation process $X_{e_1,\theta_0}$ started from $\bar p_{e_0,\theta_0}$,

$$\bar S^\tau_{e_1,\theta_0} = \lambda \int_0^\infty e^{-\lambda t}\, \mathbb E_{\bar p_{e_0,\theta_0}}\bigl[S(X_{e_1,\theta_0}(t))\bigr] dt = \lambda\, \bigl\langle \bar p_{e_0,\theta_0},\ (\lambda - \mathcal L_{e_1,\theta_0})^{-1} S \bigr\rangle,$$

a resolvent of the perturbed generator.
2. For a stressful disturbance ($\bar S_{e_0,\theta_0} > \bar S^\tau_{e_1,\theta_0}$): $R_\tau < 0$ only if the adaptation itself is detrimental; $0 < R_\tau < 1$ is the fraction of the disturbance-induced loss recovered by adapting; $R_\tau > 1$ means long-run success after adaptation exceeds the original.
3. $R_\tau$ replaces the classical recovery ratio $R = (\bar S_{e_1,\theta_1} - \min_t \mathbb E S(X(t)))/(\bar S_{e_0,\theta_0} - \min_t \mathbb E S(X(t)))$, whose worst-case term is not an ensemble average; the two differ in general but can be close.

## Expansion

Treating the reaction time as random with a known law turns the "worst state" of the classical definition into an expectation at the adaptation time, which can be computed from stationary means and one resolvent solve, or estimated from population experiments without tracking every individual's trajectory. The construction borrows linear-response and resolvent tools from non-equilibrium statistical mechanics, which also allow perturbative approximations of $R_\tau$ for small disturbances.

## Depends on

- [Strongly continuous contraction semigroups, generators and cores](../../../../../Analysis/operator-theory/strongly-continuous-contraction-semigroups.md)

## Sources

- J. M. Ramirez, J. M. Restrepo, V. Lucarini, D. Weston, "Probabilistic Measures for Biological Adaptation and Resilience", *Physical Review E* 109(2) (2024), 024413, definition of resilience through adaptation $R_\tau$ and its resolvent representation, <https://doi.org/10.1103/physreve.109.024413> (preprint arXiv:2307.06974).
