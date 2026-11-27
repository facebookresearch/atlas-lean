# Dirichlet's principle

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with no loops and with conductances $w : E \to (0, \infty)$ and [Laplacian](../graph-laplacians-and-cheeger-s-inequality/laplacian.md) $L$. If $s \ne t$ lie in the same connected component of the [underlying graph](../oriented-incidence-matrices/underlying-graph.md), then the [effective conductance](effective-conductance.md) is attained:

$$C_{\mathrm{eff}}(s, t) = \min\{x^{\mathsf T} L x : x(s) = 0,\ x(t) = 1\},$$

the minimum being attained by the normalised voltage $x = (v(s) - v)/(v(s) - v(t))$ for any $v$ with $L v = \delta_s - \delta_t$ (R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, Exercise 2.13, second display, with $F = 1 - x$, $A = \{s\}$, $Z = \{t\}$). On the path $0 - 1 - 2$ with unit conductances, $C_{\mathrm{eff}}(0, 2) = 1/2$, attained by $x = (0, 1/2, 1)$. Together with [Thomson's principle as a minimum](is-least-flow-energy.md), it gives the two dual variational formulas of Exercise 2.13.
