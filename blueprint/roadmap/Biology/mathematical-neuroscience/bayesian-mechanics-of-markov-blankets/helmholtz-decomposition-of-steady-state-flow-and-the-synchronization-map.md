# Helmholtz decomposition of steady-state flow and the synchronization map

**Setting.** States $x \in \mathbb{R}^d$ follow a Langevin equation $\dot x = f(x) + \omega$ with Gaussian white noise of diffusion matrix $\Gamma(x)$, and the associated Fokker–Planck equation has a non-equilibrium steady-state (NESS) density $p(x)$. The state is partitioned as $x = (\eta, b, \mu)$ into external, blanket and internal states.

**Statement.**
1. *(Markov blanket.)* The NESS density factorizes as

$$p(\mu, \eta, b) = p(\mu \mid b)\,p(\eta \mid b)\,p(b),$$

i.e. internal and external states are conditionally independent given blanket states.
2. *(Helmholtz decomposition.)* With surprisal $\mathfrak{J}(x) = -\log p(x)$, the flow can be written

$$f(x) = \big(Q(x) - \Gamma(x)\big)\nabla \mathfrak{J}(x) - \Lambda(x), \qquad \Lambda(x)_i = \sum_{j=1}^d \frac{\partial}{\partial x_j}\big(Q_{ij}(x) - \Gamma_{ij}(x)\big),$$

where $Q = -Q^{\mathsf T}$ is skew-symmetric (solenoidal, divergence-free flow on the level sets of $p$) and $\Gamma$ is positive semidefinite (gradient descent on surprisal that balances the fluctuations). Equivalently $p \propto e^{-\mathfrak J}$ is stationary for this flow.
3. *(Synchronization map.)* Let $\hat\mu_b = \arg\max_\mu p(\mu \mid b)$ and $\hat\eta_b = \arg\max_\eta p(\eta\mid b)$. When the map $b \mapsto \hat\mu_b$ is injective on the blanket states considered, there is a map $\sigma$ with

$$\sigma(\hat\mu_b) = \hat\eta_b,$$

so that each internal conditional mode parametrizes a belief about the external conditional mode.

## Expansion

Substituting $f$ into the stationary Fokker–Planck equation $\nabla\cdot(f p) = \nabla\cdot(\Gamma\nabla p)$ shows that the dissipative part exactly balances diffusion, while the solenoidal part $Q\nabla\mathfrak J$ (with its correction $\Lambda$) circulates along iso-probability contours and breaks detailed balance; the correction term vanishes when $Q$ and $\Gamma$ are constant. The synchronization map exists precisely when distinct blanket states with the same internal mode also share the external mode, which is guaranteed by injectivity of $b\mapsto\hat\mu_b$. Internal states flowing on variational free energy share their fixed points with the flow on surprisal, and mode matching through $\sigma$ is the sense in which the system "infers" its environment; in linear systems the external mode has no dynamics and the statement reduces to static Bayesian estimation.

## Sources

- M. J. D. Ramstead, D. A. R. Sakthivadivel, C. Heins, M. Koudahl, B. Millidge, L. Da Costa, B. Klein, K. J. Friston, "On Bayesian mechanics: a physics of and by beliefs", Interface Focus 13(3) (2023) 20220029, Section 3.3, Eqs (3.4)–(3.5), <https://doi.org/10.1098/rsfs.2022.0029>, PMCID PMC10198254.
