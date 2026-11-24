# Effective resistance is a potential difference

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with conductances $w : E \to [0, \infty)$ and [Laplacian](../graph-laplacians-and-cheeger-s-inequality/laplacian.md) $L$. Let $s \ne t$ be vertices and $v : V \to \mathbb{R}$ a potential with

$$L v = \delta_s - \delta_t$$

(one unit of current injected at $s$ and extracted at $t$). Then the [effective resistance](effective-resistance.md) is $R_{\mathrm{eff}}(s, t) = v(s) - v(t)$, and this number is positive. Equivalently $R_{\mathrm{eff}}(s, t) = (\delta_s - \delta_t)^{\mathsf T} L^{+} (\delta_s - \delta_t)$, which is how D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, Section 12.1 defines it; the computation of Section 12.2 shows that its reciprocal is the minimum energy $C_{\mathrm{eff}}(s, t)$. No connectivity hypothesis is needed: if $s$ and $t$ lie in different components, no such $v$ exists.
