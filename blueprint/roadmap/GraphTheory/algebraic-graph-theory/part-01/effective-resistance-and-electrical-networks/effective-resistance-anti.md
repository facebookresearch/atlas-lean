# Rayleigh's monotonicity law for effective resistance

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), and let $w, w' : E \to \mathbb{R}$ be conductances with $0 \le w_e \le w'_e$ for every edge $e$. If $s, t \in V$ have positive [effective conductance](effective-conductance.md) $C_{\mathrm{eff}}^{w}(s, t) > 0$ for $w$, then the [effective resistance](effective-resistance.md) satisfies

$$R_{\mathrm{eff}}^{w'}(s, t) \le R_{\mathrm{eff}}^{w}(s, t):$$

raising resistances cannot decrease an effective resistance (D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, the remark after Theorem 12.3.1).
