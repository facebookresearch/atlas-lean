# Every admissible potential bounds the effective conductance

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with conductances $w : E \to [0, \infty)$ and [Laplacian](../graph-laplacians-and-cheeger-s-inequality/laplacian.md) $L$. For $s, t \in V$ and every $x : V \to \mathbb{R}$ with $x(s) = 0$ and $x(t) = 1$,

$$C_{\mathrm{eff}}(s, t) \le x^{\mathsf T} L x,$$

where $C_{\mathrm{eff}}$ is the [effective conductance](effective-conductance.md) (D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, Section 12.2).
