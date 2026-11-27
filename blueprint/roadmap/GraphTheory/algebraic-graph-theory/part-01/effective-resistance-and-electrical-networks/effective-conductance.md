# Effective conductance

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with conductances $w : E \to \mathbb{R}$ and [Laplacian](../graph-laplacians-and-cheeger-s-inequality/laplacian.md) $L = \sum_{e} w_e (\delta_{e^-} - \delta_{e^+})(\delta_{e^-} - \delta_{e^+})^{\mathsf T}$. For $s, t \in V$, the effective conductance between $s$ and $t$ is the infimum

$$C_{\mathrm{eff}}(s, t) = \inf\{x^{\mathsf T} L x : x : V \to \mathbb{R},\ x(s) = 0,\ x(t) = 1\},$$

taken in $\mathbb{R}$ with the convention that the infimum of an empty set or of a set unbounded below is $0$ (D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, Section 12.2, where it is written $C_{\mathrm{eff}}(s, t)$). For $s = t$ no potential is admissible and $C_{\mathrm{eff}}(s, s) = 0$. For nonnegative conductances every energy $x^{\mathsf T} L x$ is nonnegative, so the infimum is a genuine infimum, and $x^{\mathsf T} L x$ is twice the spring energy when $s$ and $t$ are held at distance one; with a negative conductance the set can be unbounded below.

In R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, effective conductance is defined probabilistically as $\mathcal{C}(a \leftrightarrow z) = \pi(a) \mathbb{P}_a[\tau_z < \tau_a^+]$, equation (2.4), and Exercise 2.13 (Dirichlet's principle) shows that it equals $\min\{\sum_e c(e)(dF(e))^2 : F = 1 \text{ on } A,\ F = 0 \text{ on } Z\}$; with $F = 1 - x$ this is the infimum above, which for positive conductances on a loopless multigraph and distinct $s$, $t$ in one component is attained ([Dirichlet's principle](is-least-dirichlet-energy.md)).
