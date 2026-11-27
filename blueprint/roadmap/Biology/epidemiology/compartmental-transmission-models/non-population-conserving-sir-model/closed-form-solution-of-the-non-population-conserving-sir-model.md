# Closed-form solution of the non-population-conserving SIR model

**Model (SIR-NC).** With infection rate $\lambda > 0$ and total removal rate $\gamma > 0$ (recovery, death, quarantine), and $S(0) > 0$, $I(0) > 0$,

$$\dot S = -\lambda\,\frac{I S}{S + I}, \qquad \dot I = \lambda\,\frac{I S}{S + I} - \gamma I,$$

and any removed sub-compartment with rate $\beta < \gamma$ (for example recoveries) is recovered by quadrature, $R(t) = \beta\int_0^t I(s)\,ds$. An outbreak occurs (initially $\dot I > 0$) iff $\lambda/\gamma > 1 + I(0)/S(0)$.

**Theorem.** Let $C = S(0)/I(0)$ and $\lambda \ne \gamma$. Then

$$I(t) = I(0)\Big(\frac{1 + C e^{-(\lambda - \gamma)t}}{1 + C}\Big)^{-\frac{\lambda}{\lambda - \gamma}} e^{-\gamma t}, \qquad S(t) = S(0)\Big(\frac{e^{(\lambda - \gamma)t} + C}{1 + C}\Big)^{-\frac{\lambda}{\lambda - \gamma}},$$

and the infected curve peaks at

$$T_{\max} = \frac{\Big(\log\Big[C\,\dfrac{\lambda - \gamma}{\gamma}\Big]\Big)^+}{\lambda - \gamma}.$$

For time-dependent rates $\lambda(t), \gamma(t)$, $I(t) = I(0)\exp\Big(\int_0^t \Big[\frac{\lambda(s)\, C e^{-\int_0^s(\lambda - \gamma)}}{1 + C e^{-\int_0^s(\lambda - \gamma)}} - \gamma(s)\Big] ds\Big)$, and $T_{\max}$ solves $\int_0^{T_{\max}} (\lambda - \gamma)\,dt = \big(\log[C(\lambda(T_{\max}) - \gamma(T_{\max}))/\gamma(T_{\max})]\big)^+$.

With a constant import rate $\nu$ of infections from susceptibles, the solution remains explicit up to one convolution integral.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

The ratio $x = S/I$ satisfies $\dot x = \dot S/I - x\,\dot I/I = -\lambda x\frac{I + S}{S + I} + \gamma x = -(\lambda - \gamma)x$, so $x(t) = C e^{-(\lambda - \gamma)t}$. Substituting $S/(S + I) = x/(1 + x)$ makes the equations for $\ln I$ and $\ln S$ explicit quadratures, and $\int_0^t \frac{\lambda C e^{-(\lambda-\gamma)s}}{1 + C e^{-(\lambda-\gamma)s}}\,ds = -\frac{\lambda}{\lambda - \gamma}\ln\frac{1 + C e^{-(\lambda - \gamma)t}}{1 + C}$. The peak is where $\lambda x/(1 + x) = \gamma$, i.e. $x = \gamma/(\lambda - \gamma)$; it is at $t > 0$ iff $C(\lambda - \gamma)/\gamma > 1$, which is the outbreak condition. Unlike the population-conserving SIR model, where only an implicit first integral is available, removal shrinks the denominator and keeps the per-capita incidence a function of $S/I$ alone.

## Sources

- Vivek S. Borkar, D. Manjunath, "Revisiting SIR in the Age of COVID-19: Explicit Solutions and Control Problems", SIAM Journal on Control and Optimization 60 (2022), S370–S395, <https://doi.org/10.1137/20m1372913>. Published version of arXiv:2010.06445, cited next; locators there refer to the arXiv version.
- Vivek S. Borkar, D. Manjunath, "Revisiting SIR in the age of COVID-19: Explicit Solutions and Control Problems", arXiv (2020). Section 2 (SIR-NC model and outbreak condition), Theorem 1, Theorem 2. <https://doi.org/10.48550/arXiv.2010.06445>
