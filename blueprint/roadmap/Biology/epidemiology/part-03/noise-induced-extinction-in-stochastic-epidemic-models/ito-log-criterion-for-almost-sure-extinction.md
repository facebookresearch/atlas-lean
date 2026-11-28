# Itô-log criterion for almost-sure extinction

**Model.** Perturb each class of an SIR model with natural turnover by its own multiplicative white noise: with recruitment $\Lambda$, natural death rate $\mu$, transmission rate $\beta$, recovery rate $\gamma$, disease-induced death rate $\delta$ and noise intensities $\nu_1, \nu_2, \nu_3$ (all positive), and $W_1, W_2, W_3$ independent standard Brownian motions,

$$
\begin{aligned}
dS(t) &= \big(\Lambda - \mu S(t) - \beta S(t) I(t)\big)\, dt + \nu_1 S(t)\, dW_1(t),\\
dI(t) &= \big(\beta S(t) I(t) - (\mu + \gamma + \delta) I(t)\big)\, dt + \nu_2 I(t)\, dW_2(t),\\
dR(t) &= \big(\gamma I(t) - \mu R(t)\big)\, dt + \nu_3 R(t)\, dW_3(t).
\end{aligned}
$$

For every initial value in $\mathbb R^3_{>0}$ the solution exists for all $t \ge 0$ and stays in $\mathbb R^3_{>0}$. The noise-adjusted reproduction number is

$$\tilde R_0^{s} = \frac{\beta\Lambda}{\mu\big(\mu + \gamma + \delta + \nu_2^2/2\big)} \ <\ R_0 = \frac{\beta\Lambda}{\mu(\mu + \gamma + \delta)}.$$

**Theorem.** Assume $\mu > \tfrac12\big(\nu_1^2 \vee \nu_2^2 \vee \nu_3^2\big)$. If $\tilde R_0^s < 1$, then for every initial value in $\mathbb R^3_{>0}$, almost surely

$$\limsup_{t\to\infty} \frac{\ln I(t)}{t} \ \le\ \Big(\mu + \gamma + \delta + \frac{\nu_2^2}{2}\Big)\big(\tilde R_0^s - 1\big) \ <\ 0 .$$

Hence the infection dies out exponentially fast with probability one, even when $R_0 > 1$.

**Martingale lemma.** If $M$ is a real continuous local martingale with $M_0 = 0$ and $\langle M, M\rangle_t \to \infty$, then $M_t / \langle M, M\rangle_t \to 0$ almost surely; and if $\limsup_t \langle M,M\rangle_t / t < \infty$, then $M_t/t \to 0$ almost surely.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

By Itô's formula, $d \ln I = \big(\beta S - (\mu+\gamma+\delta) - \tfrac{\nu_2^2}{2}\big)dt + \nu_2\, dW_2$, the $-\nu_2^2/2$ being the Itô correction of the logarithm. Adding the $S$ and $I$ equations and dividing by $t$ gives $\frac1t\int_0^t S\,ds = \frac{\Lambda}{\mu} - \frac{\mu+\gamma+\delta}{\mu}\cdot\frac1t\int_0^t I\,ds + \varphi(t)$, where $\varphi(t)$ collects $(S+I)(0)/t$, $(S+I)(t)/t$ and the stochastic integrals $\frac1t\int_0^t S\,dW_1$, $\frac1t\int_0^t I\,dW_2$; these tend to $0$ almost surely (the solution grows sublinearly, and the stochastic integrals are negligible by the martingale lemma, which is where $\mu > \tfrac12(\nu_1^2 \vee \nu_2^2 \vee \nu_3^2)$ enters). Therefore

$$\frac{\ln I(t)}{t} \le \frac{\ln I(0)}{t} + \frac{\beta\Lambda}{\mu} - \Big(\mu + \gamma + \delta + \frac{\nu_2^2}{2}\Big) + \beta\varphi(t) + \frac{\nu_2 W_2(t)}{t},$$

and $W_2(t)/t \to 0$ almost surely (the martingale lemma with $\langle W_2,W_2\rangle_t = t$), which gives the bound. Noise thus acts like an extra removal rate $\nu_2^2/2$, so sufficiently large environmental fluctuations eliminate an infection that would persist deterministically. With several infected classes and delayed incidence, as in a stochastic SIRC model with a cross-immune class $C$ and incidence $\xi S(t) I(t-\tau)$, Rihan, Alsakaji and Rajivganthi apply the same argument to a positive linear combination $U = \alpha(I + C) + (\eta + \alpha)R$ of the infected and partially immune classes (their Theorem 3, assuming their stochastic threshold is below $1$ and that the turnover rate $\eta$ exceeds half the largest squared noise intensity): Itô's formula for $\ln U$ yields $\limsup_t t^{-1}\ln U \le \xi - \kappa$, with $\kappa$ built from the noise intensities and removal rates, and the stochastic integrals are again negligible by the martingale lemma.

## Sources

- C. Ji, D. Jiang, "The extinction and persistence of a stochastic SIR model", Advances in Difference Equations 2017 (2017), 30, system (1.2), Lemmas 2.1–2.2 and Theorem 2.1 (extinction), <https://doi.org/10.1186/s13662-016-1068-z>.
- F. A. Rihan, H. J. Alsakaji and C. Rajivganthi, "Stochastic SIRC epidemic model with time-delay for COVID-19", Advances in Difference Equations 2020 (2020), 502, Extinction section (Lemma 2, the martingale lemma; Lemma 3; Theorem 3, Eqs. (29)–(35)), for the delayed SIRC example in the Expansion, <https://doi.org/10.1186/s13662-020-02964-8>, PMCID: PMC7499021.
- X. Mao, *Stochastic Differential Equations and Applications*, 2nd ed., Horwood (2007), Theorem 1.3.4 (strong law of large numbers for local martingales).
