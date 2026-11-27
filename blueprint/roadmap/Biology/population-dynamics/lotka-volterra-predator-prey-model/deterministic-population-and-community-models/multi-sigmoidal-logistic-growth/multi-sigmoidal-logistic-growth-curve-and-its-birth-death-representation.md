# Multi-sigmoidal logistic growth curve and its birth–death representation

**Curve.** Let $Q_\beta(t) = \sum_{i=1}^p \beta_it^i$ with $\beta_p > 0$, $P_\beta = Q_\beta'$, $\eta > 0$ and $\theta = (\eta, \beta)$. The multi-sigmoidal logistic model is

$$\frac{d}{dt}l_m(t) = h_\theta(t)\,l_m(t), \qquad h_\theta(t) = \frac{P_\beta(t)e^{-Q_\beta(t)}}{\eta + e^{-Q_\beta(t)}}, \qquad l_m(t_0) = l_0 > 0 .$$

It integrates to

$$l_m(t) = l_0\,\frac{\eta + e^{-Q_\beta(t_0)}}{\eta + e^{-Q_\beta(t)}},$$

so $l_m(t) \to l_0\big(\eta + e^{-Q_\beta(t_0)}\big)/\eta$ as $t\to\infty$: the carrying capacity depends on the initial size, unlike the classical logistic curve. For $p = 1$ this is the logistic curve; for $p \ge 2$ the polynomial $Q_\beta$ can produce several growth phases and hence several inflection points, which fits plant growth data with multiple sigmoidal stages.

**Birth–death representation.** Let $N(t)$ be a time-inhomogeneous linear birth–death process on $\mathbb N_0$ with rates $b_n(t) = n\lambda(t)$, $d_n(t) = n\mu(t)$, with $\lambda, \mu$ positive and locally integrable. Its conditional mean $E(t) = \mathbb E[N(t) \mid N(0) = n_0]$ solves $E'(t) = \xi(t)E(t)$ with net growth rate $\xi = \lambda - \mu$.

**Proposition.** The process has conditional mean of multi-sigmoidal logistic type if and only if its net growth rate equals $h_\theta$:

$$\xi(t) = \lambda(t) - \mu(t) = h_\theta(t), \qquad t \ge 0 .$$

Any split of $h_\theta$ into birth and death rates yields such a process; the choice affects the variance (computable in closed form in special cases) and the extinction probability, a second process with quadratic rates is also analyzed, and a scaling limit gives a lognormal diffusion whose mean is of multi-sigmoidal logistic type.

## Proof sketch

Since $\frac{d}{dt}\ln(\eta + e^{-Q_\beta}) = -P_\beta e^{-Q_\beta}/(\eta + e^{-Q_\beta}) = -h_\theta$, the ODE integrates to $\ln l_m(t) - \ln l_0 = \ln(\eta + e^{-Q_\beta(t_0)}) - \ln(\eta + e^{-Q_\beta(t)})$. Because $\beta_p > 0$, $Q_\beta(t) \to \infty$ and $e^{-Q_\beta} \to 0$, giving the limit. Inflection points are zeros of $\frac{d}{dt}(h_\theta l_m)$; with a polynomial $Q_\beta$ of degree $p$, $h_\theta$ can change monotonicity several times. For the linear birth–death process, the Kolmogorov forward equations give $E' = (\lambda - \mu)E$, so $E(t) = n_0\exp\int_0^t\xi$; matching $\exp\int\xi$ with the multi-sigmoidal solution forces $\xi = h_\theta$ and conversely.

## Sources

- Antonio Di Crescenzo, Paola Paraggio, Patricia Román-Román and Francisco Torres-Ruiz, "Applications of the multi-sigmoidal deterministic and stochastic logistic models for plant dynamics", *Applied Mathematical Modelling* 92 (2021), 884–904, <https://doi.org/10.1016/j.apm.2020.11.046>. Preprint version: arXiv:2401.15727 (2024), multi-sigmoidal logistic equation, birth–death process with linear rates and the proposition characterizing its mean, <https://doi.org/10.48550/arXiv.2401.15727>.
