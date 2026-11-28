# Two-compartment biphasic decay and its identifiable combinations

**Model.** Let $E_1(t)$ and $E_2(t)$ be the labile and resistant pathogen populations in an environmental compartment, $E = E_1 + E_2$, and $u(t) \ge 0$ a known input (shedding). With decay rates $\theta_1, \theta_2$, dormancy rate $\delta_1$ (labile to resistant), resuscitation rate $\delta_2$ (resistant to labile), labile fraction $\eta$ of the input, and initial conditions (with $\theta_1, \theta_2 > 0$, $\delta_1, \delta_2 \ge 0$, $\omega > 0$, $0 < \rho \le 1$, and $0 < \eta \le 1$ when $E_1$ is observed with input) $E_1(0) = \rho\omega$, $E_2(0) = (1-\rho)\omega$,

$$\dot E_1 = -(\theta_1 + \delta_1)E_1 + \delta_2E_2 + \eta u, \qquad \dot E_2 = \delta_1E_1 - (\theta_2 + \delta_2)E_2 + (1-\eta)u .$$

Three submodels correspond to biological hypotheses: population heterogeneity ($\delta_1 = \delta_2 = 0$, $E$ observed), hardening-off ($\delta_2 = 0$, $\eta = 1$, $E$ observed) and viable-but-not-culturable ($\eta = 1$, $\theta_1 = \theta_2$, only the culturable $E_1$ observed).

**Proposition 1 (biphasic form).** Assume the system matrix has distinct eigenvalues, $(\theta_1 + \delta_1 - \theta_2 - \delta_2)^2 + 4\delta_1\delta_2 > 0$, and $\theta_1 \ne \theta_2$ when $E$ is observed, $\delta_2 \ne 0$ when $E_1$ is observed. Then each observed curve $Y \in \{E, E_1\}$ has the form

$$Y(t) = d\big(c\,e^{-at} + (1-c)\,e^{-bt}\big) + \int_0^t\big(h\,e^{-a(t-s)} + (1-h)\,e^{-b(t-s)}\big)\upsilon(s)\,ds,$$

with $\upsilon = u$ for $Y = E$ and $\upsilon = \eta u$ for $Y = E_1$, where $a > b > 0$ are the negatives of the eigenvalues of the system matrix:

$$a + b = \theta_1 + \theta_2 + \delta_1 + \delta_2, \qquad ab = (\theta_1 + \delta_1)(\theta_2 + \delta_2) - \delta_1\delta_2 .$$

For $Y = E$: $d = \omega$ and $ca + (1-c)b = \rho\theta_1 + (1-\rho)\theta_2$. For $Y = E_1$: $d = \rho\omega$ and $ca + (1-c)b = \theta_1 + \delta_1 + \delta_2(1 - 1/\rho)$.

**Proposition 2.** The apparent parameters $a, b, c, d$ (and $h$ when $\upsilon \not\equiv 0$ is measured) are identifiable from the curve $Y$.

**Proposition 3.** The full model is structurally unidentifiable from $E$ (if $\theta_1 \ne \theta_2$) and from $E_1$ (if $\delta_2 \ne 0$): it has six parameters (seven with a known input), while the data determine only four (five) independent combinations, those fixed by $a, b, c, d$ (and $h$).

**Proposition 4.** From a measured concentration curve and input, one cannot decide whether the measurement is the total population $E$ with $\upsilon = u$ or only the labile (culturable) population $E_1$ with $\upsilon = \eta u$.

## Expansion

The system is linear with a $2 \times 2$ constant matrix $M$, so every coordinate and every sum of coordinates is a combination of $e^{-at}$ and $e^{-bt}$, plus the convolution of the input with the impulse response; normalizing the impulse response to $1$ at $t = 0$ defines $h$, and $Y'(0)/Y(0)$ gives the stated weighted rates. Sums of distinct exponentials have identifiable exponents and coefficients, which yields Proposition 2; matching the five apparent parameters with the mechanistic ones then shows which pairs of parameters must be known independently (for example both decay rates) to resolve the rest, and that knowing other pairs (for example $\delta_1$ and $\rho$) does not suffice. Under population heterogeneity $a = \theta_1$, $b = \theta_2$, $c = \rho$, $d = \omega$, $h = \eta$; but a hardening-off or viable-but-not-culturable model with suitable parameters produces the same curve, so sampling studies alone cannot determine the mechanism, while measured-input experiments make the submodels identifiable. Misattributing a biphasic tail can bias microbial risk estimates and hydrological fate-and-transport predictions.

## Sources

- A. F. Brouwer, M. C. Eisenberg, J. V. Remais, P. A. Collender, R. Meza and J. N. Eisenberg, "Modeling biphasic environmental decay of pathogens and implications for risk analysis", Environmental Science & Technology (2017), Eqs. (4)–(9), Propositions 1–4 and Corollary 1, <https://doi.org/10.1021/acs.est.6b04030>, PMCID PMC5789392.
