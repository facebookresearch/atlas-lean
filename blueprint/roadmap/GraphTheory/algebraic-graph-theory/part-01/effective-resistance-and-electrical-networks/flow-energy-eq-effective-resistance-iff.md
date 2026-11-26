# Thomson's principle, equality case

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with conductances $w : E \to (0, \infty)$ and [Laplacian](../graph-laplacians-and-cheeger-s-inequality/laplacian.md) $L$. Let $s \ne t$ be vertices and $v : V \to \mathbb{R}$ a potential with $L v = \delta_s - \delta_t$. A [unit flow](is-unit-flow.md) $\theta$ from $s$ to $t$ has [energy](flow-energy.md) exactly $R_{\mathrm{eff}}(s, t)$ if and only if it is the unit current

$$\theta_e = w_e \big(v(e^-) - v(e^+)\big) \quad (e \in E);$$

every other unit flow has strictly larger energy (R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, Section 2.4, Thomson's principle: $\mathcal{E}(\theta) > \mathcal{E}(i)$ unless $\theta = i$).
