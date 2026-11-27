# Mortality dominance obstructs global chemostat stabilization

For the chemostat with mortality $\dot X = (p_0\mu(S) - b - D)X$, $\dot S = D(S_{\mathrm{in}}-S) - \mu(S)X$ on $(0,\infty)\times(0,S_{\mathrm{in}})$ and an equilibrium $(X^*, S^*)$ obtained with dilution $D^* > 0$, suppose there is $\bar S \in (S^*, S_{\mathrm{in}})$ with

$$ p_0\mu(S_{\mathrm{in}}) < p_0\mu(\bar S) < b \qquad \text{and} \qquad \mu'(S) \le 0 \ \text{ for all } S \in [\bar S, S_{\mathrm{in}}] . $$

**Theorem.** Then no nonnegative locally Lipschitz feedback $D(X,S) \ge 0$ globally stabilizes $(X^*, S^*)$: for every such feedback the closed-loop system has unbounded solutions in the logarithmic coordinates, i.e. solutions that leave every compact subset of the open quadrant.

**Haldane kinetics.** For $\mu(S) = MS/(K + S + aS^2)$ with $M, K, a > 0$ the dichotomy is sharp up to the balanced case: if $p_0\mu(S_{\mathrm{in}}) > b$ the fortified feedback achieves global stabilization, and if $p_0\mu(S_{\mathrm{in}}) < b$ global stabilization by a positive feedback is impossible. The same holds for any unimodal $C^1$ growth rate, including all concave ones.

## Depends on

- [Global feedback stabilization of the chemostat with mortality](global-feedback-stabilization-of-the-chemostat-with-mortality.md)

## Expansion

Heuristically, when the substrate is near $S_{\mathrm{in}}$, mortality exceeds the maximal net growth available on $[\bar S, S_{\mathrm{in}}]$, so the biomass decreases there whatever the dilution. Since dilution can only push $S$ toward $S_{\mathrm{in}}$ and consumption is weak at low biomass, initial conditions with small $X$ and $S$ close to $S_{\mathrm{in}}$ remain in this strip while $X \to 0$, which in logarithmic coordinates is an unbounded trajectory. The monotonicity condition on $\mu$ prevents escape toward smaller $S$ through faster consumption.

## Sources

- Iasson Karafyllis, Epiphane Loko, Miroslav Krstić, Antoine Chaillet, "Global stabilisation of chemostats with nonzero mortality and substrate dynamics", International Journal of Control 99 (2026), 3122–3142, <https://doi.org/10.1080/00207179.2026.2713102>. Published version of arXiv:2502.09310, cited next; locators there refer to the arXiv version.
- I. Karafyllis, E. Loko, M. Krstic, A. Chaillet, "Global Stabilization of Chemostats with Nonzero Mortality and Substrate Dynamics", arXiv:2502.09310 (2025), Section 2 (Theorem 2 and the Haldane discussion) and Section 5.2 (proof of Theorem 2). <https://doi.org/10.48550/arXiv.2502.09310>
