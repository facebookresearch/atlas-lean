# Effective resistance as minimum energy (Thomson's principle)

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with no loops and with conductances $w : E \to (0, \infty)$. If $s \ne t$ lie in the same connected component of the [underlying graph](../oriented-incidence-matrices/underlying-graph.md), then

$$R_{\mathrm{eff}}(s, t) = \min\Big\{\sum_{e \in E} \frac{\theta_e^2}{w_e} : \theta \text{ a unit flow from } s \text{ to } t\Big\},$$

the minimum being attained by the unit current, where $R_{\mathrm{eff}}$ is the [effective resistance](effective-resistance.md) and unit flows are as in [this definition](is-unit-flow.md) (R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, Exercise 2.13, first display).

Together with [Dirichlet's principle](is-least-dirichlet-energy.md), which shows that the infimum defining [effective conductance](effective-conductance.md) is a minimum over potentials, this gives the duality between Thomson's and Dirichlet's principles in Exercise 2.13, for $A = \{s\}$ and $Z = \{t\}$ (the source's displays are for vertex sets): the least energy of a unit flow is the reciprocal of the least energy of a potential that is $0$ at $s$ and $1$ at $t$. On the path $0 - 1 - 2$ with unit conductances, $R_{\mathrm{eff}}(0, 2) = 2$, attained by the unit flow $1$.
