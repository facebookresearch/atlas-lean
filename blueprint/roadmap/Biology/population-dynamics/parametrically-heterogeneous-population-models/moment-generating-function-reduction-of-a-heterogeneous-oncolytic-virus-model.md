# Moment-generating-function reduction of a heterogeneous oncolytic virus model

**Homogeneous model.** Uninfected tumour cells $X$ and virus-infected tumour cells $Y$ (rescaled by the carrying capacity and the uninfected growth rate) satisfy

$$\dot X = X\big(1 - (X + Y)\big) - \beta\frac{XY}{X + Y}, \qquad \dot Y = \gamma Y\big(1 - (X + Y)\big) + \beta\frac{XY}{X + Y} - \delta Y,$$

with relative growth rate of infected cells $\gamma$, transmission coefficient $\beta$ (frequency-dependent infection) and virus-induced death rate $\delta$; virus abundance is taken proportional to infected cells.

**Heterogeneous model.** Uninfected cells carry individual susceptibilities $\beta \in B \subseteq [0, \infty)$ with density $x(t, \beta)$, $X(t) = \int_B x(t,\beta)\,d\beta$:

$$\partial_t x(t, \beta) = x(t,\beta)\big(1 - (X + Y)\big) - \beta\, x(t, \beta)\frac{Y}{X + Y}, \qquad \dot Y = \gamma Y\big(1 - (X + Y)\big) + E_\beta(t)\frac{XY}{X + Y} - \delta Y,$$

with $x(0,\beta) = X_0\, p(0, \beta)$ and $E_\beta(t) = \int_B \beta\, x(t,\beta)\,d\beta / X(t)$ the current mean susceptibility.

**Theorem (exact reduction).** Let $M(\lambda) = \int_B e^{\lambda\beta} p(0, \beta)\, d\beta$ be the moment generating function of the initial susceptibility distribution and define the auxiliary variable

$$\dot q = -\frac{Y}{X + Y}, \qquad q(0) = 0 .$$

Then

$$E_\beta(t) = \frac{M'(q(t))}{M(q(t))} = \frac{d}{d\lambda}\ln M(\lambda)\Big|_{\lambda = q(t)},$$

and $(X, Y, q)$ solve the closed ODE system obtained from the homogeneous model by replacing $\beta$ with $E_\beta(t)$; the density itself is $x(t, \beta) = X_0\, p(0,\beta)\, e^{\beta q(t)}\exp\!\int_0^t \big(1 - X - Y\big)ds$, so $p(t, \beta) = p(0,\beta)e^{\beta q(t)}/M(q(t))$. The mean susceptibility is nonincreasing, $\dot E_\beta = \mathrm{Var}_t(\beta)\,\dot q \le 0$.

**Gamma example.** If $p(0, \cdot)$ is a gamma distribution with shape $k$ and rate $s$ shifted to $[\eta, \infty)$, then $\beta$ stays gamma distributed with

$$E_\beta(t) = \eta + \frac{k}{s - q(t)},$$

and if infected cells persist ($Y \ge c > 0$), $q(t) \to -\infty$ and $E_\beta(t) \to \eta$, the minimal susceptibility in the initial support.

## Expansion

Because $\beta$ enters the per-capita rate of uninfected cells linearly, each $\beta$-class grows by a common factor times $e^{\beta q(t)}$, so the distribution at time $t$ is the exponential tilting of the initial one by $q(t)$, and all its moments follow from $M$; the reduction is exact, not a moment closure. Differentiating $E_\beta(t) = (\ln M)'(q(t))$ gives $\dot E_\beta = \frac{d^2}{d\lambda^2}\ln M\,\big|_{q}\,\dot q$, and the second derivative of a cumulant generating function is the variance. Biologically, selection removes highly susceptible tumour cells, so the effective transmission declines during therapy, and the long-run behaviour is governed by the homogeneous model at $\beta = \eta$; transient phases, such as apparent tumour reduction followed by relapse, can be read off by tracking $E_\beta(t)$ across the bifurcation diagram of the homogeneous model.

## Sources

- G. P. Karev, A. S. Novozhilov, E. V. Koonin, "Mathematical modeling of tumor therapy with oncolytic viruses: effects of parametric heterogeneity on cell dynamics", Biology Direct 1 (2006) 30, sections on the homogeneous model (equations (1)–(2)) and the inhomogeneous model (equations (3)–(6), gamma-distributed initial susceptibility), <https://doi.org/10.1186/1745-6150-1-30>.
