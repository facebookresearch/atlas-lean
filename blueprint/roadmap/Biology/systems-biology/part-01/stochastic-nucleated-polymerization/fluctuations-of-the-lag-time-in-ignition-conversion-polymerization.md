# Fluctuations of the lag time in ignition–conversion polymerization

**Model.** In a volume $V$ (with $V_A$ the volume times Avogadro's number), $M_V$ monomers $\mathcal X$ are converted to polymerized form $\mathcal Y$ by two reactions,

$$
\mathcal X+\mathcal X\xrightarrow{\ \alpha/V_A^2\ }2\mathcal Y\quad\text{(ignition)},\qquad \mathcal X+\mathcal Y\xrightarrow{\ \beta/V_A^2\ }2\mathcal Y\quad\text{(conversion)}.
$$

Let $X_V(t)$ be the number of free monomers and, for $\delta\in(0,1)$, $T_V(\delta)=\inf\{t>0:X_V(t)\le(1-\delta)M_V\}$ the time to reach completion degree $\delta$.

**Proposition (law of large numbers).** If $M_V/V_A\to m>0$, then $\overline X_V(t)=X_V(V_At)/V_A$ converges in distribution to the solution of $\dot{\bar x}=-\alpha\bar x^2-\beta\bar x(m-\bar x)$, $\bar x(0)=m$, namely

$$
\bar x(t)=m\,\frac{\beta}{\alpha}\,\frac{1}{e^{\beta mt}-1+\beta/\alpha}.
$$

**Proposition (central limit theorem).** If $M_V=mV_A+o(\sqrt{V_A})$, then $\big(X_V(V_At)-V_A\bar x(t)\big)/(m\sqrt{V_A})$ converges to the Gaussian process $U$ solving a linear SDE with $U(0)=0$, drift $-\beta m\,\frac{e^{\beta mt}+1-\beta/\alpha}{e^{\beta mt}-1+\beta/\alpha}\,U$ and diffusion coefficient $\frac{\beta\sqrt\alpha\sqrt{e^{\beta mt}+1}}{\alpha e^{\beta mt}+\beta-\alpha}$.

**Theorem (completion time).** Under the same scaling,

$$
\frac{T_V(\delta)}{V_A}\to t_\delta=\frac{1}{\beta m}\log\Big(1+\frac{\beta\delta}{\alpha(1-\delta)}\Big),\qquad \frac{T_V(\delta)-V_At_\delta}{\sqrt{V_A}}\to\frac{U(t_\delta)}{m\,[\alpha(1-\delta)^2+\beta\delta(1-\delta)]}.
$$

When $\alpha\ll\beta$, $T_V(\delta)\approx V_At_\delta+\sqrt{V_A}\,\mathcal N\big(0,\tfrac{3}{2M_V\alpha\beta m^2}\big)$, so the standard deviation of the lag time scales like $1/\big(m\sqrt{M_V\alpha\beta}\big)$, independent of $\delta$.

## Expansion

This is a density-dependent Markov jump process, so Kurtz's theorems give the fluid limit and Gaussian fluctuations; the logistic-type ODE is explicitly solvable. The completion time is the hitting time of level $(1-\delta)m$, so its fluctuations are those of $U$ divided by the fluid speed $|\dot{\bar x}(t_\delta)|$, which yields the denominator. Solving the linear SDE explicitly shows that almost all variance is generated early, during ignition, when few polymers exist; once conversion dominates, trajectories run parallel. This explains experimentally observed large lag-time variability with nearly identical growth phases, and gives the variance–rate relation used to estimate $\alpha\beta$ from replicate kinetic curves.

## Depends on

- [Stochastic mass-action propensity](../../stochastic-mass-action-metabolic-control-and-flu/propensity.md)

## Proof depends on

- [Kurtz's law of large numbers for density-dependent chains](../../../../Probability/markov-chains/density-dependent-markov-chains/kurtz-law-of-large-numbers-for-density-dependent.md)
- [Kurtz's diffusion approximation for density-dependent chains](../../../../Probability/markov-chains/density-dependent-markov-chains/kurtz-diffusion-approximation-clt-for-density-de.md)

## Sources

- Sarah Eugene, Wei-Feng Xue, Philippe Robert, Marie Doumic-Jauffret, "Insights into the variability of nucleated amyloid polymerization by a minimalistic model of stochastic protein assembly", arXiv:1510.03982: Section "A Phenomenological Stochastic Model": Proposition 1 (law of large numbers), Proposition 2 (central limit theorem), the theorem on asymptotics of the time for degree of reaction completion and its variance corollary; Supplemental Material (explicit solution of the SDE and the alpha much smaller than beta asymptotics). <https://doi.org/10.48550/arXiv.1510.03982>
