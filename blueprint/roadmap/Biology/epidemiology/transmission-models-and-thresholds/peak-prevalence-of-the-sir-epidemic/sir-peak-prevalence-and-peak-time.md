# Peak prevalence and peak time of the SIR epidemic

Consider the normalized SIR model $\dot S = -\beta S I$, $\dot I = \beta S I - \gamma I$, $\dot R = \gamma I$ with $\beta, \gamma > 0$, $S(0), I(0) > 0$, $S(0) + I(0) + R(0) = 1$, and $R_0 = \beta / \gamma$. Suppose $S(0) > R_0^{-1}$, so that $I$ initially increases.

**Peak height (Equations 34, 37).** $I$ attains its maximum when $S = S_p = R_0^{-1}$, and

$$I_p = I(0) + S(0) - R_0^{-1}\big(1 + \ln(R_0 S(0))\big);$$

for an epidemic started from $S(0) \approx 1$, $I(0) \approx 0$ this gives $I_p \approx 1 - R_0^{-1}(1 + \ln R_0)$, a function of $R_0$ alone.

**Linearizing time change (Equations 39–41).** Define $\tau$ by $d\tau/dt = I(t)$, $\tau(0) = 0$. Then $dS/d\tau = -\beta S$, $dI/d\tau = \beta S - \gamma$, $dR/d\tau = \gamma$ is linear, with solution

$$S = S(0) e^{-\beta\tau}, \qquad I = I(0) + S(0)\big(1 - e^{-\beta\tau}\big) - \gamma\tau, \qquad R = R(0) + \gamma\tau,$$

valid for $0 \le \tau < \int_0^\infty I(s)\, ds$. The peak occurs at $\tau_p = \ln(R_0 S(0)) / \beta$, i.e. at physical time

$$t_p = \int_0^{\tau_p} \frac{d\tau'}{I(0) + S(0)\big(1 - e^{-\beta\tau'}\big) - \gamma\tau'} .$$

## Proof depends on

- [Conserved quantity behind the final-size relation](../../kermack-mckendrick-sir-model/susceptible-mul-exp-eq.md)

## Expansion

$\dot I = I(\beta S - \gamma)$ vanishes only at $S = \gamma/\beta$, and since $S$ is strictly decreasing it crosses this value once, so the peak is unique. Dividing $\dot I$ by $\dot S$ gives $dI/dS = -1 + (R_0 S)^{-1}$, which integrates to $I - I(0) = -(S - S(0)) + R_0^{-1} \ln(S / S(0))$; substituting $S_p$ yields $I_p$. In the new clock $\tau$, which measures accumulated infection pressure, the bilinear term $SI$ disappears, giving the explicit solution; the peak in $\tau$ is where $S(0) e^{-\beta\tau} = \gamma/\beta$. All the dependence on $I$ is pushed into the time change, which is why $t_p$ is an integral rather than a closed form. The paper uses these formulas, together with the early exponential approximation $I(t) \approx I(0) e^{(\beta S(0) - \gamma)t}$, to explain a linear trade-off between start time and duration of an optimal single social-distancing pulse.

## Sources

- M. Sadeghi, J. M. Greene, E. D. Sontag, "Universal features of epidemic models under social distancing guidelines", Annual Reviews in Control 51 (2021) 426–440, Appendix A, Equations (33)–(41), <https://doi.org/10.1016/j.arcontrol.2021.04.004> (PMC8063609).
