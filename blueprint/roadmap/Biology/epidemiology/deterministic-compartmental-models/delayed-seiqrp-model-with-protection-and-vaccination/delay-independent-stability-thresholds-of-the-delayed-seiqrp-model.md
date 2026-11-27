# Delay-independent stability thresholds of the delayed SEIQRP model

**Model.** In proportions of a population with equal birth and death rate $b$, let $s, e, i, q, r, p$ be susceptible, exposed, infectious, quarantined, recovered and protected (insusceptible) fractions, with incubation of the infection process modelled by a delay $\tau \ge 0$:

$$\begin{aligned}
\dot s &= b - \beta s(t-\tau)i(t-\tau) - (\alpha + b)s, & \dot e &= \beta s(t-\tau)i(t-\tau) - (\gamma + b)e,\\
\dot i &= \gamma e - (\delta + b)i, & \dot q &= \delta i - (\lambda + b)q,\\
\dot r &= \lambda q - br, & \dot p &= \alpha s - bp,
\end{aligned}$$

with $\beta$ transmission, $\alpha$ protection, $\gamma$ progression, $\delta$ quarantine and $\lambda$ recovery rates, all positive. The disease-free equilibrium is $\Sigma_0 = (\tfrac{b}{\alpha+b}, 0,0,0,0, \tfrac{\alpha}{\alpha+b})$, the endemic one has $s^+ = (\delta+b)(\gamma+b)/(\beta\gamma)$, and

$$R_0 = \frac{\beta\gamma b}{(\alpha+b)(\delta+b)(\gamma+b)} .$$

**Theorem (disease-free equilibrium).** If $R_0 < 1$, $\Sigma_0$ is locally asymptotically stable for every delay $\tau \ge 0$; if $R_0 > 1$, it is unstable for every $\tau \ge 0$.

**Theorem (endemic equilibrium).** For $\tau = 0$ and $R_0 > 1$ the endemic equilibrium $\Sigma^+$ is locally asymptotically stable. For $\tau > 0$ it remains locally asymptotically stable provided

$$1 < R_0 < \min\Big(3,\ 1 + \frac{\sqrt{(\alpha+b)^2 + (\delta+b)^2 + (\gamma+b)^2}}{\alpha+b}\Big) \quad\text{and}\quad M_1R_0^2 + M_2R_0 + M_3 > 0,$$

where $M_1 = -(\alpha+b)^2[(\delta+b)^2 + (\gamma+b)^2]$, $M_2 = 2(\alpha+b)^2[(\delta+\gamma+2b)^2 - 3(\delta+b)(\gamma+b)] + 2(\alpha+b)(\delta+b)(\gamma+b)(\delta+\gamma+2b)$ and $M_3 = 2(\alpha+b)(\delta+b)(\gamma+b)(\alpha - \delta - \gamma - b)$.

**Vaccination.** Adding a vaccinated class $w$ with $\dot s$ losing $us$ and $\dot w = us - bw$ ($u$ the vaccination rate) gives

$$\tilde R_0 = \frac{\beta\gamma b}{(\alpha + u + b)(\delta+b)(\gamma+b)},$$

and the same delay-independent dichotomy holds for the disease-free equilibrium with $\tilde R_0$ in place of $R_0$.

## Proof sketch

Only the $(s,e,i)$ block matters for stability, since $q, r, p$ are driven linearly. At $\Sigma_0$ the delayed term enters only through $\beta s_0 i(t-\tau)$, and the characteristic equation reduces to $(y + \gamma + b)(y + \delta + b) = \beta\gamma s_0 e^{-\tau y}$; for $R_0 < 1$ Rouché's theorem shows that no root crosses the imaginary axis as $\tau$ grows, while for $R_0 > 1$ there is a positive real root for every $\tau$. At $\Sigma^+$, the conditions on $R_0$ exclude purely imaginary roots $y = i\omega$ of the delayed characteristic polynomial for all $\omega$, so stability at $\tau = 0$ persists for all delays.

## Sources

- Mohamed A. Zaitri, Cristiana J. Silva and Delfim F. M. Torres, "Stability Analysis of Delayed COVID-19 Models", *Axioms* 11 (2022), 400, <https://doi.org/10.3390/axioms11080400>. Preprint version: arXiv:2208.06649 (2022), Sections 2–3 (normalized SEIQRP model, equilibria, $R_0$, stability theorems for the model with and without vaccination), <https://doi.org/10.48550/arXiv.2208.06649>.
