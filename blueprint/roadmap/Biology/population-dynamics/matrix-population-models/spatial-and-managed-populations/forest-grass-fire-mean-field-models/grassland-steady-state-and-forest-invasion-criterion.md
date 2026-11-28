# Grassland steady state and forest invasion criterion

**Model.** Land cover fractions of forest $F$, grass $G$, burning $B$ and ash $A$, with $F+G+B+A=1$, follow the nonspatial mean-field limit of a spatial stochastic forest-fire (FGBA) model:

$$\begin{aligned}
\dot F&=(\varphi_GG+\varphi_AA)F-\beta_FBF-\Phi_F(G)F-\mu F,\\
\dot G&=\gamma A+\mu F-\varphi_GFG-\Phi_G(G)G-\beta_GBG,\\
\dot B&=\Phi_G(G)G+\Phi_F(G)F+(\beta_GG+\beta_FF)B-qB,\\
\dot A&=qB-\gamma A-\varphi_AFA.
\end{aligned}$$

Here $\varphi_G,\varphi_A$ are forest seeding rates into grass and ash, $\mu$ is non-fire forest mortality (forest reverting to grass), $\beta_G,\beta_F$ are fire-spread rates, $q$ is the fire quenching rate, $\gamma$ the ash-to-grass recovery rate, and $\Phi_G,\Phi_F\ge0$ are smooth nondecreasing sigmoidal flammability functions of grass cover (spontaneous ignitions). Grass flammability is strictly positive, $\Phi_G>0$ on $(0,1]$ (as for the source's sigmoids with positive baseline ignition rate $g_0$); without it the fire-free all-grass state $G=1$, $B=A=0$ is a further steady state on $F=0$. All rates are positive.

**Grassland subsystem.** On $F=0$, eliminating $A=1-G-B$ gives $\dot G=\gamma(1-G-B)-\Phi_G(G)G-\beta_GBG$, $\dot B=\Phi_G(G)G+\beta_GGB-qB$; the simplex $\{G,B\ge0,\ G+B\le1\}$ is forward invariant, and steady states solve

$$\Phi_G(\bar G)=(1-\bar G)\frac{\gamma q}{\gamma+q}\Big(\frac1{\bar G}-\frac{\beta_G}{q}\Big).$$

**Results.**

1. If $\Phi_G>0$ on $(0,1]$, then for all positive $\gamma,q,\beta_G$ there is a unique grass-burning-ash (GBA) steady state, and $\bar G<q/\beta_G$.
2. The GBA steady state is linearly stable to perturbations within $\{F=0\}$ for all parameter values.
3. It is stable to invasion by forest exactly when

$$\beta_F\bar B+\Phi_F(\bar G)+\mu>\varphi_G\bar G+\varphi_A\bar A .$$

## Expansion

The right side of the steady-state equation is strictly decreasing in $\bar G$ on $(0,q/\beta_G)$, blowing up at $0$ and vanishing at $q/\beta_G$ or $1$, while $\Phi_G$ is nondecreasing and strictly positive there, so the curves cross exactly once, strictly before the right side vanishes. The $2\times2$ Jacobian on $F=0$ has negative trace (since $\bar G<q/\beta_G$) and positive determinant (since the slope of $\Phi_G$ exceeds the negative slope of the right side), so Routh-Hurwitz gives stability. On the full system the Jacobian at $F=0$ is block lower triangular, and the forest direction has eigenvalue equal to the per capita forest growth rate $\varphi_G\bar G+\varphi_A\bar A-\beta_F\bar B-\Phi_F(\bar G)-\mu$. Forest is excluded when fire-driven and natural tree mortality outweigh seeding into grass and ash; when the inequality reverses, forest invades, and coexistence of a stable grassland with a stable forest state (bistability) arises from the sigmoidal flammability.

## Sources

- Kimberly Shen, Simon Levin, Denis D. Patterson, "Spatial modeling of forest-savanna bistability: Impacts of fire dynamics and timescale separation", *Journal of Mathematical Biology* 92(3) (2026), 44, Propositions 1-3 and Theorem 1 (Section 3.1), <https://doi.org/10.1007/s00285-026-02363-9> (preprint arXiv:2505.01149).
