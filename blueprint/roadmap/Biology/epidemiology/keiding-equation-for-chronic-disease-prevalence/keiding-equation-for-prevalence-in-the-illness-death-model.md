# Keiding's equation for prevalence in the illness–death model with duration-dependent mortality

**Setting.** In the illness–death model of an irreversible chronic disease, healthy people aged $a$ at calendar time $t$ acquire the disease with incidence $i(t,a)$ and die with mortality $m_0(t,a)$; diseased people die with mortality $m_1(t,a,d)$ that may also depend on the disease duration $d$. Everyone is born healthy, there is no migration, and the rates are smooth. Healthy counts $S(t,a)$ and diseased counts by duration $C(t,a,d)$ satisfy

$$(\partial_t + \partial_a)S = -(m_0 + i)S, \qquad (\partial_t + \partial_a + \partial_d)C = -m_1 C, \qquad C(t,a,0) = i(t,a)S(t,a),$$

and the age-specific prevalence is $p = C^\star/(C^\star + S)$ with $C^\star(t,a) = \int_0^a C(t,a,\delta)\,d\delta$. Write

$$\mathcal{M}_{t,a}(y) = \exp\Big(-\int_0^y \big(m_0 + i\big)(t-a+\tau,\tau)\,d\tau\Big), \qquad M_1(t,a,d) = \int_0^d m_1(t-d+\tau,\ a-d+\tau,\ \tau)\,d\tau .$$

**Proposition (Keiding's equation).**

$$p(t,a) = \frac{\int_0^a i(t-\delta, a-\delta)\,\mathcal{M}_{t,a}(a-\delta)\,e^{-M_1(t,a,\delta)}\,d\delta}{\mathcal{M}_{t,a}(a) + \int_0^a i(t-\delta, a-\delta)\,\mathcal{M}_{t,a}(a-\delta)\,e^{-M_1(t,a,\delta)}\,d\delta},$$

which does not depend on the number of newborns.

**Corollaries.**
1. If $m_1$ does not depend on $d$, the number of cases solves $(\partial_t + \partial_a)C^\star = -m_1 C^\star + iS$, and $p$ satisfies the nonlinear PDE $(\partial_t + \partial_a)p = (1-p)\big(i - p(m_1 - m_0)\big)$, equivalently the linear PDE for the prevalence odds $\pi = p/(1-p)$: $(\partial_t + \partial_a)\pi = i - \pi(m_1 - m_0 - i)$.
2. If the incidence does not depend on calendar time, then for every $t$, with $N = S + C^\star$ and $M_0(t,a) = \int_0^a m_0(t-a+\tau,\tau)\,d\tau$,

$$i(a) = \partial_a\Big(\ln S_0(t-a) - \ln\big(1 - p(t,a)\big) - \ln N(t,a) - M_0(t,a)\Big),$$

so the incidence can be estimated from prevalence, demographic data (births $S_0$, population $N$) and the mortality of the non-diseased, without knowing the possibly complex mortality $m_1(t,a,d)$ of the diseased.

## Expansion

Both PDEs are transport equations along cohort lines $t - a = \text{const}$ (and $t - d$, $a - d$ fixed for the duration variable), so the method of characteristics gives $S(t,a) = S_0(t-a)\,\mathcal{M}_{t,a}(a)$ and $C(t,a,d) = i(t-d,a-d)\,S(t-d,a-d)\,e^{-M_1(t,a,d)}$; integrating over duration and dividing gives Keiding's ratio, in which the newborn count cancels. Corollary 2 uses that the cumulative hazard $I(t,a)$ of the healthy satisfies $\ln S(t,a) = \ln S_0(t-a) - M_0(t,a) - I(t,a)$ and $S = (1-p)N$. It suggests a paradoxical study design: to estimate incidence, follow up the mortality of healthy people rather than of the diseased.

## Sources

- Ralph Brinks, "On Keiding's Equation and its relation to differential equations about prevalence and incidence in chronic diseases", arXiv:1606.08162 (2016), Section 1 (Keiding's odds formula, Proposition 1), Section 2 (PDEs), Section 3 (independence from disease duration), Section 4 (incidence independent of calendar time, Remarks 1–2), <https://doi.org/10.48550/arXiv.1606.08162>.
