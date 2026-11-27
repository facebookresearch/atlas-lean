# Adaptive regulation of the contact rate in prolonged SIR epidemics

**Setting.** In an SIR epidemic in a large population, let the contact rate $\beta(t)$ respond to prevalence: society relaxes towards a desired rate that falls as infections rise,

$$\dot S = -c\,\beta S I, \qquad \dot I = c\,\beta S I - \gamma I, \qquad \dot\beta = -\alpha\big(g(\beta) - h(uI)\big),$$

where $\alpha > 0$ is the adaptation speed, $u > 0$ is a control "knob" scaling the perceived severity of the disease, and (A1) $g, h$ are $C^1$, (A2) $h$ is positive and strictly decreasing, (A3) $g$ is nonnegative and strictly increasing. When susceptibles are many times more numerous than infectives, write $S = \tilde S/\varepsilon$; then $\tilde S$ is slow and, on the fast time scale with $c_s = c\,S$ frozen, the dynamics reduce to

$$\dot I = c_s\,\beta I - \gamma I, \qquad \dot\beta = -\alpha\big(g(\beta) - h(uI)\big).$$

Assume (A4) $g(\gamma/c_s)$ lies in the interior of the range of $h$.

**Theorem.**
1. If the endemic steady state exists, the disease-free steady state of the reduced system is exponentially unstable.
2. Under (A1)–(A4) the reduced system has a unique positive steady state

$$(I_e,\beta_e) = \Big(\frac{h^{-1}\big(g(\gamma/c_s)\big)}{u},\ \frac{\gamma}{c_s}\Big),$$

which is globally asymptotically stable on the open orthant and locally exponentially stable.
3. (Singular perturbation.) By Tikhonov's theorem, on any finite slow-time window the full model stays within $O(\varepsilon)$ of the fast system tracking this quasi-steady state while the slow variable $\tilde S$ decreases at rate $\tilde c\,\beta_e\,\tilde S\,I_e$.
4. (Adaptation and fold-change detection.) The contact rate always returns to $\beta_e = \gamma/c_s$ regardless of $u$, and with $\beta$ as output the system has the fold-change detection property: its response to a step in $u$ depends only on the ratio of the new to the old value.
5. (Set-point control.) To hold infectives at a target quasi-steady level $I^\ast > 0$, choose $u = h^{-1}\big(g(\gamma/c_s)\big)/I^\ast$.

## Expansion

At the endemic state the infection grows exactly when $c_s\beta > \gamma$, so the infective equation acts as an integral controller on the contact rate: integrating $\dot{\log I} = c_s\beta - \gamma$ forces $\beta \to \gamma/c_s$, the value at which the effective reproduction number equals one, independent of the perception parameter; this is perfect adaptation. Global stability uses the logarithmic coordinate $p = \log I$ and a Lyapunov function combining $\int (h(ue^{p_e}) - h(ue^{p}))\,dp$ with $\int (\beta - \beta_e)$-type terms; the Jacobian at the endemic state has characteristic polynomial $\lambda^2 + \alpha g'(\beta_e)\lambda - c_s I_e\alpha u\,h'(uI_e)$ with positive coefficients, so Routh–Hurwitz gives local exponential stability. Fold-change detection follows from the invariance of the reduced system under $I \mapsto (u_1/u_2) I$, because $u$ only enters through the product $uI$. The model explains long plateaus of prevalence in prolonged outbreaks: susceptible depletion is slow, and behavioural feedback holds the epidemic near criticality, with the plateau height set by public perception.

## Sources

- M. Ali Al-Radhawi, Mahdiar Sadeghi, Eduardo D. Sontag, "Long-Term Regulation of Prolonged Epidemic Outbreaks in Large Populations via Adaptive Control: A Singular Perturbation Approach", IEEE Control Systems Letters 6 (2022), 578–583, <https://doi.org/10.1109/lcsys.2021.3083983>. Published version of arXiv:2103.08488, cited next; locators there refer to the arXiv version.
- M. Ali Al-Radhawi, Mahdiar Sadeghi, Eduardo D. Sontag, "Long-term regulation of prolonged epidemic outbreaks in large populations via adaptive control: a singular perturbation approach", arXiv:2103.08488 (2021), Section 2 (contact-rate regulation and time-scale separation), Section 3 (assumptions A1–A4, Proposition 1, Theorem 1, Proposition 2) and Section 4 (PI-controller interpretation, Theorem 2, Proposition 3), <https://doi.org/10.48550/arXiv.2103.08488>.
