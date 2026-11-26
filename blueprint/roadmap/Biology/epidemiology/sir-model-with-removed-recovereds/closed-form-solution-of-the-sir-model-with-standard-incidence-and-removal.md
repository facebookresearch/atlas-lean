# Closed-form solution of the SIR model with standard incidence and removal

**Model.** Let $S, I, R \ge 0$ be the susceptible, infective and recovered fractions, with recovered individuals removed from the mixing population, so that the incidence is standard with respect to the active population $S + I$:

$$\dot S = -\frac{\beta S I}{S + I}, \qquad \dot I = \frac{\beta S I}{S + I} - \alpha I, \qquad \dot R = \alpha I,$$

with transmission rate $\beta > 0$, recovery rate $\alpha > 0$, $\beta \ne \alpha$, and initial data $S(0) = S_0 > 0$, $I(0) = I_0 > 0$, $R(0) = 0$, $S_0 + I_0 = 1$.

**Theorem.** With $\tau = (\beta - \alpha)^{-1}$, the solution is

$$S(t) = S_0\Big(\frac{S_0 + I_0}{S_0 + I_0 e^{t/\tau}}\Big)^{\beta\tau}, \qquad I(t) = I_0\Big(\frac{S_0 + I_0}{S_0 + I_0 e^{t/\tau}}\Big)^{\beta\tau} e^{t/\tau}, \qquad R(t) = 1 - \frac{(S_0 + I_0)^{\beta\tau}}{(S_0 + I_0 e^{t/\tau})^{\beta\tau - 1}}.$$

$S$ and $R$ are generalized logistic functions and $I$ is a generalized logistic function times an exponential, all with the same characteristic time $\tau$. If $\beta > \alpha$ and $S_0/I_0 > (\beta/\alpha - 1)^{-1}$, the infective curve has a single peak at

$$t_{\mathrm{peak}} = \tau \log\Big(\frac{S_0}{I_0}\Big(\frac{\beta}{\alpha} - 1\Big)\Big).$$

**Proposition (curve crossings).** Let $\beta > \alpha$, $S_0 > I_0 > 0$ and $S_0 > \alpha/\beta$. Then any two of the curves $S(t)$, $I(t)$, $R(t)$ intersect exactly once. Moreover:

1. $S$ and $I$ cross before the infection peak if $\beta > 2\alpha$, at the peak if $\beta = 2\alpha$, and after it if $\beta < 2\alpha$;
2. the three curves meet at a common point iff $\beta/\alpha < \log 3/(\log 3 - \log 2)$ and $S_0 = \tfrac13 (3/2)^{\beta/\alpha}$;
3. they meet exactly at the infection peak iff $\beta = 2\alpha$ and $S_0 = \tfrac34$.

## Expansion

The ratio $x = I/S$ satisfies $\dot x = x\,\big(\beta I/(S+I) - \alpha + \beta S/(S+I)\big) = (\beta - \alpha)x$, so $I/S = (I_0/S_0)e^{t/\tau}$. Substituting $I = S x$ into $\dot S = -\beta S x/(1 + x)$ gives a separable equation with solution $S = S_0\big((1 + x_0)/(1 + x)\big)^{\beta\tau}$, which is the stated formula; $R$ follows from $S + I + R = 1$. The infection peaks when $\beta S/(S + I) = \alpha$. The differences from the classical SIR dynamics are traced to the zeroes of the two models' conserved quantities, and the paper also obtains closed forms for some realistic time-dependent transmission rates.

## Sources

- A. Ballesteros, A. Blasco and I. Gutierrez-Sagredo, "Exact closed-form solution of a modified SIR model", arXiv:2007.16069 (2020), Section 2 (exact solution), Section 3 (peak time and Proposition 2), <https://doi.org/10.48550/arXiv.2007.16069>.
