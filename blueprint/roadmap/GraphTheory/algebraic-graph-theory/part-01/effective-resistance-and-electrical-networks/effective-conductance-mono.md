# Rayleigh's monotonicity law

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), and let $w, w' : E \to \mathbb{R}$ be conductances with $0 \le w_e \le w'_e$ for every edge $e$. Then for all $s, t \in V$ the [effective conductance](effective-conductance.md) satisfies

$$C_{\mathrm{eff}}^{w}(s, t) \le C_{\mathrm{eff}}^{w'}(s, t):$$

lowering conductances (raising resistances) cannot increase an effective conductance (D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, Theorem 12.3.1).

This is part (i) of Rayleigh's Monotonicity Principle in R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, Section 2.4, for $A = \{s\}$ and $Z = \{t\}$. Lyons and Peres derive it from Thomson's principle; it also follows directly from Dirichlet's principle, since every potential has no larger energy for the smaller conductances.

## Background

- [Thomson's principle](effective-resistance-le-flow-energy.md): the flow-side variational principle from which Lyons and Peres derive this law.
