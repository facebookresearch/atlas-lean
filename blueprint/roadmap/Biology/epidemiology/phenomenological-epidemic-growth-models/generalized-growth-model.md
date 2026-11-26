# Generalized-growth model

**Model.** The cumulative number of cases $C(t) > 0$ satisfies

$$C'(t) = r\,C(t)^{p}, \qquad C(0) = C_0 > 0 \qquad \text{(Eq. 1)},$$

with growth rate $r > 0$ and deceleration-of-growth parameter $p \in [0,1]$; $C'(t)$ is the incidence.

**Proposition (explicit solution).**

- If $p = 1$: $C(t) = C_0 e^{rt}$ (exponential growth).
- If $0 \le p < 1$:

$$C(t) = \Big(C_0^{\,1-p} + (1-p)\,r\,t\Big)^{1/(1-p)}, \qquad t \ge 0 .$$

In particular $p = 0$ gives constant incidence $C'(t) = r$ and linear $C(t) = C_0 + rt$; for $0 < p < 1$, $C(t)$ grows like $t^{1/(1-p)}$, i.e. polynomially, and the incidence grows like $t^{p/(1-p)}$.

**Diagnostic.** On a semi-logarithmic scale exponential growth is a straight line, while $p < 1$ produces downward curvature of $\log C'(t)$; systematic, autocorrelated residuals of an exponential fit to early data indicate sub-exponential growth.

**Fitting.** Parameters $\Theta = (r, p)$ are estimated by nonlinear least squares, $\hat\Theta = \arg\min_\Theta \sum_{i=1}^{n} w_{t_i}\big(f(t_i,\Theta) - y_{t_i}\big)^2$, with $w_{t_i} \equiv 1$ (ordinary), $w_{t_i} = 1/y_{t_i}$, or exponential-smoothing weights $w_{t_{n-i}} = \alpha(1-\alpha)^{i-1}$, $0 < \alpha < 1$, that favor recent observations.

## Expansion

For $p < 1$ separate variables: $C^{-p}\,dC = r\,dt$ integrates to $C^{1-p}/(1-p) = rt + C_0^{1-p}/(1-p)$, which gives the formula; writing it as $C(t) = C_0\big(1 + (1-p)\,r\,t\,C_0^{\,p-1}\big)^{1/(1-p)}$ shows that it tends to $C_0 e^{rt}$ as $p \to 1$. Fitting the model to the first 15 weeks of the 2014–16 Ebola epidemic in Sierra Leone, the source obtains $r = 0.81$ and $p = 0.48$, i.e. polynomial early growth, while the exponential model leaves autocorrelated residuals.

## Sources

- G. Chowell, "Fitting dynamic models to epidemic outbreaks with quantified uncertainty: A primer for parameter uncertainty, identifiability, and forecasts", Infectious Disease Modelling 2(3) (2017) 379–398, Sections 2.1.1, 5–6, Eq. 1, <https://doi.org/10.1016/j.idm.2017.08.001> (PMC5726591).
- C. Viboud, L. Simonsen and G. Chowell, "A generalized-growth model to characterize the early ascending phase of infectious disease outbreaks", Epidemics 15 (2016) 27–37.
