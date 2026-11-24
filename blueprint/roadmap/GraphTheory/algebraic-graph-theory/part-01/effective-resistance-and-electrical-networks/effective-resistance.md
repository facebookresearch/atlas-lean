# Effective resistance

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with conductances $w : E \to \mathbb{R}$. For $s, t \in V$ the effective resistance is the reciprocal of the [effective conductance](effective-conductance.md),

$$R_{\mathrm{eff}}(s, t) = \frac{1}{C_{\mathrm{eff}}(s, t)},$$

read as $0$ when $C_{\mathrm{eff}}(s, t) = 0$, for instance when $s = t$ or when $s$ and $t$ lie in different connected components (D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, Section 12.2, $R_{\mathrm{eff}}(s, t) = 1/C_{\mathrm{eff}}(s, t)$).
