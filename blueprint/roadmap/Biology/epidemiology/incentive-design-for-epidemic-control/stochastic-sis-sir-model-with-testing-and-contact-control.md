# Stochastic SIS–SIR model with testing and controlled contact rate

Fix a horizon $T > 0$, a birth rate $\lambda \ge 0$, a natural death rate $\mu \ge 0$, a disease death rate $\gamma \ge 0$, recovery rates $\nu \ge 0$ (back to susceptible) and $\rho \ge 0$ (to permanent immunity), and a volatility $\sigma > 0$. A government testing policy is a predictable process $\alpha_t$ with values in a set $A$ bounded and bounded below by some $\varepsilon > 0$; a population contact policy is a predictable process $\beta_t \in B = [0, \beta_{\max}]$. Under the measure $\mathbb P^{\alpha,\beta}$ with Brownian motion $W^\beta$, the susceptible and infected proportions satisfy

$$dS_t = (\lambda - \mu S_t + \nu I_t - \beta_t\sqrt{\alpha_t}\, S_t I_t)\,dt + \sigma\alpha_t S_t I_t\,dW^\beta_t,$$

$$dI_t = \bigl(\beta_t\sqrt{\alpha_t}\, S_t I_t - (\mu + \nu + \gamma + \rho) I_t\bigr)\,dt - \sigma\alpha_t S_t I_t\,dW^\beta_t, \tag{4.5}$$

with $(S_0, I_0) = (s_0, i_0) \in (0, \infty)^2$. The testing level enters the transmission drift through $\sqrt{\alpha_t}$ and the volatility through $\alpha_t$ itself, so for $\alpha_t < 1$ testing reduces the noise more than the effective transmission rate. The case $\nu = 0$ is an SIR model, $\rho = 0$ an SIS model, and both positive give an SIR model with partial immunity (SISRS). The measure $\mathbb P^{\alpha,\beta}$ is obtained from the uncontrolled law $\mathbb P^\alpha$ (the same equations with $\beta = 0$ and Brownian motion $W$) by the [Girsanov change of measure](../../../Probability/stochastic-calculus/it-s-formula/girsanov-change-of-measure-for-bounded-drift.md) with the bounded kernel $\theta_t = -\beta_t/(\sigma\sqrt{\alpha_t})$, $|\theta_t| \le \beta_{\max}/(\sigma\sqrt{\varepsilon})$, and $W^\beta_t = W_t - \int_0^t \theta_r\,dr$: the noise term $\pm\sigma\alpha_t S_t I_t\,dW_t$ of $\mathbb P^\alpha$ then produces the transmission drift $\mp\beta_t\sqrt{\alpha_t}\,S_t I_t$.

**A priori bound.** For admissible $\alpha$ (unique weak solution with $(S, I)$ nonnegative), almost surely for all $t \in [0, T]$,

$$0 \le S_t + I_t = e^{-\mu t}(s_0 + i_0) + \int_0^t e^{-\mu(t-s)}\bigl(\lambda - (\gamma + \rho)I_s\bigr)ds \le F(t, s_0, i_0),$$

$$F(t, s, i) = e^{-\mu t}(s + i) + \lambda\Bigl(\frac{1 - e^{-\mu t}}{\mu}\mathbf 1_{\{\mu > 0\}} + t\,\mathbf 1_{\{\mu = 0\}}\Bigr), \tag{4.3, 4.4}$$

so $S$ and $I$ are bounded, and strictly positive if $s_0, i_0 > 0$. In the SIR case $R_t = r_0 e^{-\mu t} + \rho\int_0^t I_s e^{-\mu(t-s)}ds$ is a functional of the path of $I$ and need not be a state variable.

## Depends on

- [Girsanov's theorem for bounded progressive drift](../../../Probability/stochastic-calculus/it-s-formula/girsanov-change-of-measure-for-bounded-drift.md)

## Proof depends on

- [Exponential martingale for bounded integrands](../../../Probability/stochastic-calculus/it-s-formula/exponential-martingale-for-bounded-integrands.md)
- [Variation-of-constants solution of a linear relaxation equation](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/relaxation.md)

## Expansion

The transmission term $\beta\sqrt{\alpha}\,SI$ is driven by a single Brownian motion that enters $S$ and $I$ with opposite signs, a stochastic perturbation of the transmission rate. Adding the two equations cancels both the transmission and the noise, so $S + I$ solves the linear random ODE $d(S + I) = (\lambda - \mu(S + I) - (\gamma + \rho)I)\,dt$. Pathwise variation of constants, with the continuous production rate $\lambda - (\gamma + \rho)I_t$, gives the identity, and dropping the nonpositive $-(\gamma + \rho)I$ term gives the bound $F$. Because $\beta$ is bounded and $\alpha$ is bounded away from $0$, the Girsanov kernel is bounded and the stochastic exponential defining $d\mathbb P^{\alpha,\beta}/d\mathbb P^\alpha$ is a true martingale with moments of all orders. Changing the contact rate is then a change of measure, the standard weak formulation for moral hazard in which the government observes $(S, I)$ but not $\beta$. The degenerate diffusion (rank-one volatility for a two-dimensional state, with drift not in the range of the volatility) rules out the usual contract-theory structure condition. That is why the incentive problem needs its own representation.

## Sources

- E. Hubert, T. Mastrolia, D. Possamaï and X. Warin, "Incentives, lockdown, and testing: from Thucydides' analysis to the COVID-19 pandemic", Journal of Mathematical Biology 84 (2022), 37, Section 2.1 (testing policy: linear effect on the volatility, square-root effect on the transmission rate) and Section 4.1 (Equations (4.1)–(4.5), Remarks 4.2–4.3), <https://doi.org/10.1007/s00285-022-01736-0>, PMCID PMC8995008.
