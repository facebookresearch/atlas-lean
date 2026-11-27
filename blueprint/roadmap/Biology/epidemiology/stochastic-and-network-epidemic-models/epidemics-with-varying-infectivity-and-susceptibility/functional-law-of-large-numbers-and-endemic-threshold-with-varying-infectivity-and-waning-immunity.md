# Functional law of large numbers and endemic threshold with varying infectivity and waning immunity

**Model.** In a population of $N$ individuals, each infection of an individual draws an independent random infectivity function $\lambda(t)$ and susceptibility function $\gamma(t)$ of the time $t$ since that infection: the individual is infectious with intensity $\lambda(t)$ during its infectious period $[0, \eta)$, has zero susceptibility while infected, and then regains susceptibility gradually along $\gamma(t) \uparrow \gamma_*$. Infections occur at rate (susceptibility of the target) $\times$ (average force of infection). Let $\overline{\mathfrak S}^N(t)$ be the average susceptibility and $\overline{\mathfrak F}^N(t)$ the average force of infection, $\bar\lambda(t) = \mathbb E[\lambda(t)]$, and $R_0 = \int_0^\infty \bar\lambda(t)\,dt$.

**Theorem.**
1. *(FLLN.)* $(\overline{\mathfrak S}^N, \overline{\mathfrak F}^N) \to (x, y)$ in probability in $D^2$, where $(x, y)$ is the unique solution of

$$\begin{aligned}
x(t) &= \mathbb E\Bigl[\gamma_0(t)e^{-\int_0^t\gamma_0(r)y(r)dr}\Bigr] + \int_0^t \mathbb E\Bigl[\gamma(t-s)e^{-\int_s^t \gamma(r-s)y(r)dr}\Bigr]x(s)y(s)\,ds,\\
y(t) &= \bar I(0)\bar\lambda_0(t) + \int_0^t \bar\lambda(t-s)x(s)y(s)\,ds,
\end{aligned}$$

($\gamma_0, \lambda_0$ describe the initially infected and initial susceptibilities).
2. *(Disease-free threshold.)* If $\gamma$ is a.s. nondecreasing and $R_0 < \mathbb E[1/\gamma_*]$, then $(x(t), y(t)) \to (\overline{\mathfrak S}_*, 0)$: the epidemic dies out.
3. *(Endemic equilibrium.)* If $R_0 > \mathbb E[1/\gamma_*]$, susceptibility reaches $\gamma_*/2$ after an integrable time, and $(x, y)$ converges, then either the limit is disease-free or $x_* = 1/R_0$ and $y_* > 0$ is the unique positive solution of

$$\int_0^\infty \mathbb E\Bigl[\exp\Bigl(-\int_0^s\gamma(r/y_*)\,dr\Bigr)\Bigr]ds = R_0,$$

in which case the infected proportion converges to $\bar I_* = \mathbb E[\eta]\,y_*/R_0$. At $R_0 = \mathbb E[1/\gamma_*]$ only the disease-free limit is possible.

## Expansion

The threshold $\mathbb E[1/\gamma_*]$ replaces the classical $1$: if recovered individuals end up with susceptibility $\gamma_*$, a fully re-susceptible population can sustain transmission only if one infection produces enough secondary contacts to compensate the reduced susceptibility, averaged as $\mathbb E[1/\gamma_*]$ by the random final level. At an endemic equilibrium, each new infection must on average produce exactly one more, which forces the mean susceptibility to $1/R_0$; the equation for $y_*$ balances the expected time until reinfection, as susceptibility recovers under a constant force $y_*$, against the infectious contribution. With $\gamma = \mathbf 1_{t \ge \zeta}$ the model reduces to a non-Markovian SIRS model, and with exponential periods to the classical SIRS ODE.

## Sources

- Raphaël Forien, Guodong Pang, Étienne Pardoux and Arsene Brice Zotsa-Ngoufack, "Stochastic epidemic models with varying infectivity and waning immunity", The Annals of Applied Probability 35 (2025), 2175–2216, <https://doi.org/10.1214/25-aap2170>; numbering as in arXiv:2210.04667: Theorems 3.1, 3.2, 4.1, 4.2 and Corollary 4.1.
