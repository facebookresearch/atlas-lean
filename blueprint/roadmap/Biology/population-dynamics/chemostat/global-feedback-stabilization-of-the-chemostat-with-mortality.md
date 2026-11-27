# Global feedback stabilization of the chemostat with mortality

Consider the chemostat with biomass $X > 0$, substrate $S \in (0, S_{\mathrm{in}})$, yield coefficient $p_0 > 0$, mortality rate $b \ge 0$ and dilution rate $D > 0$ as the control input,

$$ \dot X = \big(p_0\mu(S) - b - D\big) X, \qquad \dot S = D(S_{\mathrm{in}} - S) - \mu(S) X , $$

where $\mu$ is bounded and $C^1$ on $[0,\infty)$ with $\mu(0) = 0$ and $\mu(S) > 0$ for $S > 0$. Fix a target dilution $D^* > 0$ with equilibrium $(X^*, S^*) \in (0,\infty)\times(0,S_{\mathrm{in}})$, so $p_0\mu(S^*) = b + D^*$ and $X^* = D^*(S_{\mathrm{in}} - S^*)/\mu(S^*)$. Under constant dilution this equilibrium is unstable whenever $\mu'(S^*) < 0$ (substrate inhibition, e.g. Haldane kinetics).

**Theorem.** Assume (A): $p_0\mu(S) > b$ for all $S \in [S^*, S_{\mathrm{in}}]$. Then for every $\delta > 0$ and $\alpha \in [0,1)$ the positive, locally Lipschitz feedback

$$ D(X,S) = \frac{D^*\mu(S)X}{\mu(S^*)X^*} + \frac{\delta b}{\mu(S^*)^{1+\alpha}}\, \big|\mu(S) - \mu(S^*)\big|^{1+\alpha}\, \mathbf{1}_{\{S \le S^*\}} $$

makes $(X^*, S^*)$ globally asymptotically stable on the whole open quadrant $(0,\infty)\times(0,S_{\mathrm{in}})$; if moreover $\alpha > 0$, the equilibrium is also locally exponentially stable. For $b = 0$ the feedback reduces to $D = p_0\mu(S)X/X^*$ (the equilibrium gives $p_0\mu(S^*) = D^*$), which is the known law $D = \mu(S)X/X^*$ when $p_0 = 1$.

## Depends on

- [Chemostat equilibria and the washout threshold](chemostat-equilibria-and-washout.md)

## Expansion

The logarithmic coordinates $x_1 = \ln\big(\mu(S^*)X/(D^*(S_{\mathrm{in}}-S))\big)$ and $x_2 = \ln\big(S(S_{\mathrm{in}}-S^*)/(S^*(S_{\mathrm{in}}-S))\big)$ map the open state space diffeomorphically onto $\mathbb{R}^2$ and the equilibrium to the origin, so global stability on $\mathbb{R}^2$ is global stability for all positive concentrations. The first feedback term cancels the substrate equation's coupling as in the mortality-free case; the second, nonnegative and bounded term raises the dilution when the substrate is depleted ($S < S^*$), which prevents biomass from being trapped in nutrient-poor states where mortality would drive it to extinction. A control Lyapunov function built in these coordinates, with assumption (A) guaranteeing net growth on $[S^*, S_{\mathrm{in}}]$, proves global attractivity.

## Sources

- Iasson Karafyllis, Epiphane Loko, Miroslav Krstić, Antoine Chaillet, "Global stabilisation of chemostats with nonzero mortality and substrate dynamics", International Journal of Control 99 (2026), 3122–3142, <https://doi.org/10.1080/00207179.2026.2713102>. Published version of arXiv:2502.09310, cited next; locators there refer to the arXiv version.
- I. Karafyllis, E. Loko, M. Krstic, A. Chaillet, "Global Stabilization of Chemostats with Nonzero Mortality and Substrate Dynamics", arXiv:2502.09310 (2025), Section 2 (lumped chemostat model with mortality; Fact 1, assumption (A) and Theorem 1) and Section 5.1 (proof of Theorem 1). <https://doi.org/10.48550/arXiv.2502.09310>
