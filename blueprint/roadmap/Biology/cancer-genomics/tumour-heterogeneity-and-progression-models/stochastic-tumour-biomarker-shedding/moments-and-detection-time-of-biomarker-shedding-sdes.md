# Moments and detection time of biomarker-shedding SDEs

**Setting.** A tumour with an immune-evasive subpopulation $E$ and an immune-sensitive subpopulation $B$, sharing a carrying capacity $K$ and attacked by T cells $I$, follows the two-prey, one-predator Lotka–Volterra system

$$\dot E = rE\Big(1 - \frac{E + pB}{K}\Big) - \alpha EI,\qquad \dot B = \gamma B\Big(1 - \frac{qE + B}{K}\Big) - \beta BI,\qquad \dot I = aEI + bBI - \delta I .$$

A circulating biomarker such as ctDNA is shed at a rate $f(t) = f(E(t), B(t), I(t))$ that is a nonnegative linear combination of the apoptotic terms $\alpha EI, \beta BI$ and the crowding (necrotic) terms, and is cleared at first-order rate $\eta > 0$. Measurement and biological noise are modeled by one of two SDEs with $C(0) = c_0 > 0$:

$$\text{(multiplicative)}\quad dC = (f(t) - \eta C)\,dt + \sigma C\,dW_t, \qquad \text{(square root)}\quad dC = (f(t) - \eta C)\,dt + \sigma\sqrt{C}\,dW_t .$$

**Theorem (moments).** Let $m(t) = \mathbb{E}\,C(t)$ and $v(t) = \operatorname{Var} C(t)$. In both models

$$m(t) = c_0 e^{-\eta t} + \int_0^t f(s)\,e^{-\eta(t-s)}\,ds .$$

For multiplicative noise the solution exists, is unique and positive, and

$$v(t) = c_0^2 e^{(\sigma^2 - 2\eta)t} + \int_0^t 2\,e^{(\sigma^2 - 2\eta)(t-s)}\,m(s) f(s)\,ds - m(t)^2;$$

for square-root noise

$$v(t) = c_0^2 e^{-2\eta t} + \int_0^t \big(2f(s) + \sigma^2\big)\,e^{-2\eta(t-s)}\,m(s)\,ds - m(t)^2 .$$

**Lemma (mean time to detection).** For the multiplicative model with detection threshold normalized to $1$, let $\tau = \inf\{t > 0 : C(t) \ge 1\}$ and $k(t,x) = \mathbb{E}[\tau - t \mid C_t = x]$. Then $k$ is the minimal nonnegative solution of the backward equation

$$\partial_t k + (f(t) - \eta x)\,\partial_x k + \tfrac12 \sigma^2 x^2\,\partial_{xx} k = -1 \quad \text{on } [0,\infty) \times (0,1), \qquad k(t,1) = 0,$$

and $\mathbb{E}[\tau \mid C(0) = c_0] = k(0, c_0)$. When the tumour–immune system is near equilibrium, $f \equiv f^*$, this reduces to a second-order ODE in $x$ solved by quadrature with $p(x) = 2(f^* - \eta x)/(\sigma^2 x^2)$ and $q(x) = -2/(\sigma^2 x^2)$.

## Expansion

Because the drift is affine in $C$ and the shedding rate $f$ is a deterministic function of time supplied by the ODE, taking expectations gives the linear ODE $\dot m = f - \eta m$. Itô's formula gives $d(C^2) = \big(2C(f - \eta C) + \sigma^2 C^2\big)dt + \text{martingale}$ for multiplicative noise, so $\mathbb{E}C^2$ solves $\dot y = (\sigma^2 - 2\eta)y + 2fm$, and $\big(2C(f - \eta C) + \sigma^2 C\big)dt$ for square-root noise, giving $\dot y = -2\eta y + (2f + \sigma^2)m$; variation of constants yields the formulas. Multiplicative noise represents a roughly constant coefficient of variation at moderate concentrations, square-root noise the Poisson sampling limit near the detection threshold. Under multiplicative noise the variance grows without bound when $\sigma^2 > 2\eta$ even if the tumour is stable. The detection-time equation is the standard Dynkin/Feynman–Kac characterization of exit times, linking hidden tumour–immune states (escape equilibria, coexistence, immune control) to observable biomarker detection delays.

## Sources

- P. Shrestha, Y. Fan, J. T. George, "Coupled SDE-ODE modeling of tumor-immune dynamics to infer biomarker release", Bulletin of Mathematical Biology (2026), model (1)–(3), Table 2, Theorem 1 (Table 3), Theorems 3–5 (Eqs 6–8), Lemma 6 (Eqs 9–10) and Theorem 7 (Eq 11), <https://doi.org/10.1007/s11538-026-01665-9>, PMCID PMC13290969.
