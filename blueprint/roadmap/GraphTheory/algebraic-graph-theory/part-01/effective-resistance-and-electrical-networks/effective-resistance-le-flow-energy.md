# Thomson's principle

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with no loops and with conductances $w : E \to (0, \infty)$. For distinct vertices $s \ne t$, every [unit flow](is-unit-flow.md) $\theta$ from $s$ to $t$ has [energy](flow-energy.md) at least the [effective resistance](effective-resistance.md):

$$R_{\mathrm{eff}}(s, t) \le \sum_{e \in E} \frac{\theta_e^2}{w_e}$$

(R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, Section 2.4, Thomson's principle with $A = \{s\}$, $Z = \{t\}$, combined with equation (2.7)).

Lyons and Peres state Thomson's principle for flows between disjoint vertex sets $A$ and $Z$; this is the case of two vertices and unit flows, and flows of strength $k$ between two vertices follow by scaling. Without loops, a unit flow forces the existence of a potential with $L v = \delta_s - \delta_t$ (the ranges of the Laplacian and of the incidence matrix coincide). The strict inequality for flows other than the current is [Thomson's principle, equality case](flow-energy-eq-effective-resistance-iff.md).
