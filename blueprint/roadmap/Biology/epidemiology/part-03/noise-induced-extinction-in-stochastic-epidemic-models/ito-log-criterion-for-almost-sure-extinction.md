# Itô-log criterion for almost-sure extinction

**Model.** Perturb the transmission dynamics of an epidemic with natural death or turnover by multiplicative white noise. In the prototype, $S, I \ge 0$ are population fractions with $S(t) + I(t) + R(t) \le 1$, and the infected class obeys

$$dI(t) = \big(\beta S(t) I(t) - (\mu + \gamma) I(t)\big)\, dt + \nu\, I(t)\, dW(t),$$

with $\beta, \mu, \gamma, \nu > 0$ and $W$ a standard Brownian motion; $S$ and $R$ may carry their own independent noises. The noise-adjusted reproduction number is

$$R_0^{s} = \frac{\beta}{\mu + \gamma + \nu^2/2} \ <\ R_0 = \frac{\beta}{\mu + \gamma}.$$

**Theorem.** For any positive initial condition, almost surely

$$\limsup_{t\to\infty} \frac{\ln I(t)}{t} \ \le\ \beta - \Big(\mu + \gamma + \frac{\nu^2}{2}\Big).$$

Hence if $R_0^s < 1$ the infection dies out exponentially fast with probability one, even when $R_0 > 1$.

**Martingale lemma.** If $M$ is a real continuous local martingale with $M_0 = 0$ and $\langle M, M\rangle_t \to \infty$, then $M_t / \langle M, M\rangle_t \to 0$ almost surely; and if $\limsup_t \langle M,M\rangle_t / t < \infty$, then $M_t/t \to 0$ almost surely.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

By Itô's formula, $d \ln I = \big(\beta S - (\mu+\gamma) - \tfrac{\nu^2}{2}\big)dt + \nu\, dW$, the $-\nu^2/2$ being the Itô correction of the logarithm. Integrating and using $S \le 1$,

$$\frac{\ln I(t)}{t} \le \frac{\ln I(0)}{t} + \beta - (\mu + \gamma) - \frac{\nu^2}{2} + \frac{\nu W(t)}{t},$$

and $W(t)/t \to 0$ almost surely by the strong law for Brownian motion (the martingale lemma with $\langle W,W\rangle_t = t$). Noise thus acts like an extra removal rate $\nu^2/2$, so sufficiently large environmental fluctuations eliminate an infection that would persist deterministically. With several infected classes and delayed incidence, as in a stochastic SIRC model with a cross-immune class $C$ and incidence $\xi S(t) I(t-\tau)$, the same argument is applied to a positive linear combination $U = \alpha(I + C) + (\eta + \alpha)R$ of the infected and partially immune classes: Itô's formula for $\ln U$ yields $\limsup_t t^{-1}\ln U \le \xi - \kappa$, with $\kappa$ built from the noise intensities and removal rates, and the stochastic integrals are again negligible by the martingale lemma, provided the turnover rate $\eta$ exceeds half the largest squared noise intensity so that the moments of the solution stay controlled.

## Sources

- F. A. Rihan, H. J. Alsakaji and C. Rajivganthi, "Stochastic SIRC epidemic model with time-delay for COVID-19", Advances in Difference Equations 2020 (2020), 502, Extinction section (Lemmas 2–3, Theorem 3, Eqs. (29)–(35)), <https://doi.org/10.1186/s13662-020-02964-8>, PMCID: PMC7499021.
- X. Mao, *Stochastic Differential Equations and Applications*, 2nd ed., Horwood (2007), Theorem 1.3.4 (strong law of large numbers for local martingales).
