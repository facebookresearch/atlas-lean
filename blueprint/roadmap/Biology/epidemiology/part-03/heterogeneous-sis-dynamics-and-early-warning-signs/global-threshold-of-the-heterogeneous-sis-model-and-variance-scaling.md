# Global threshold of the heterogeneous SIS model and variance scaling near outbreak

**Model.** Individuals have a heterogeneity state $\omega$ in a measure space $\Omega$ with population density $f(\omega)$. Susceptible and infected densities $S(t,\omega) + I(t,\omega) = f(\omega)$ evolve by

$$\partial_tI(t,\omega) = \big(\beta(\omega)J(t) + \eta(\omega)\big)\big(f(\omega) - I(t,\omega)\big) - \gamma(\omega)I(t,\omega), \qquad J(t) = \int_\Omega q(\omega)I(t,\omega)\,d\omega,$$

where $q > 0$ almost everywhere weighs each h-state's contribution to the force of infection (normalized so that $\int qf = 1$), $\beta(\omega)$ is the transmission rate, $\gamma(\omega)$ the recovery rate (both bounded and bounded below by some $\varepsilon > 0$) and $\eta(\omega)\ge0$ a bounded external import rate of infection. Write $\eta > 0$ if $\eta f > 0$ on a set of positive measure, and $\eta = 0$ otherwise.

**Theorem.**

1. (With import.) If $\eta > 0$, there is a unique steady state, and it is globally asymptotically stable.
2. (Without import.) If $\eta = 0$, let

$$R_0 = \int_\Omega q(\omega)f(\omega)\frac{\beta(\omega)}{\gamma(\omega)}\,d\omega.$$

If $R_0\le1$, the disease-free state $I\equiv0$ is the unique steady state and is globally asymptotically stable. If $R_0 > 1$ there are exactly two steady states: $I\equiv0$, which is unstable, and an endemic state $I^\ast(\omega) = \frac{f(\omega)\beta(\omega)J^\ast}{\beta(\omega)J^\ast + \gamma(\omega)}$, with $J^\ast > 0$ the unique positive root of $\int_\Omega\frac{q f\beta}{\beta J + \gamma}\,d\omega = 1$, which is globally asymptotically stable for all initial data with $I_0\not\equiv0$.
3. (Separable infectivity.) More generally, if the expected total infectivity of an individual in h-state $\omega$ towards a susceptible in h-state $\zeta$ factorizes as $a(\zeta)b(\omega)$, the next-generation operator has rank one and $R_0 = \int_\Omega a(\omega)b(\omega)S(\omega)\,d\omega$ for the disease-free susceptible density $S$.
4. (Critical slowing down.) For the homogeneous model with additive noise and a slowly drifting transmission rate, $\dot I = \beta I(1 - I) - \gamma I + \sigma\xi(t)$, $\dot\beta = \epsilon$, the linearization near the disease-free branch below threshold is an Ornstein–Uhlenbeck process $\dot{\mathcal I} = (\beta - \gamma)\mathcal I + \sigma\xi$, whose stationary variance

$$\mathrm{Var}(\mathcal I) = \frac{\sigma^2}{2(\gamma - \beta)} = \frac{\sigma^2}{2\gamma(1 - R_0)}$$

diverges as $R_0 = \beta/\gamma\nearrow1$; this power law with exponent $-1$ is an early warning sign of the transcritical (outbreak) bifurcation, valid outside an $O(\epsilon^{1/2})$ neighborhood of the bifurcation point.

## Expansion

For fixed $J(t)$ the equation for each $\omega$ is linear and relaxes towards $f(\beta J + \eta)/(\beta J + \eta + \gamma)$, which is increasing in $J$; integrating against $q$ gives a scalar monotone feedback for $J$, from which $J(t)$ converges and the sign of $\partial_tI$ is determined pointwise. Steady states correspond to fixed points of $J\mapsto\int\frac{qf(\beta J + \eta)}{\beta J + \eta + \gamma}$, a concave increasing map: with $\eta > 0$ it has a unique positive fixed point, and with $\eta = 0$ its slope at $0$ is $R_0$, so a positive fixed point exists iff $R_0 > 1$. Thus heterogeneity changes the threshold only through the weighted average defining $R_0$, not the qualitative global dynamics. Near threshold the linear decay rate $\gamma - \beta$ of perturbations vanishes, so fluctuations driven by noise are damped ever more weakly.

## Sources

- Andreas Widder, Christian Kuehn, "Heterogeneous population dynamics and scaling laws near epidemic outbreaks", arXiv (2014). Section 3 (heterogeneous model), Section 4 (Theorem 1, Lemma 1, Proposition 1), Section 5.3 (warning signs for the fast–slow stochastic model). <https://doi.org/10.48550/arXiv.1411.7323>. Published version: Mathematical Biosciences and Engineering 13(5) (2016), 1093–1118, <https://doi.org/10.3934/mbe.2016032>; locators above refer to the arXiv version.
