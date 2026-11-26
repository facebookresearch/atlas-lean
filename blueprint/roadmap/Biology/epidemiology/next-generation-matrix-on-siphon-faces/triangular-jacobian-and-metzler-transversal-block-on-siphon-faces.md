# Triangular Jacobian and Metzler transversal block on siphon faces

**Setting.** Let $\dot x = f_x(x,y)$, $\dot y = f_y(x,y)$ be a positive ODE on $\mathbb{R}^{m+n}_{\ge 0}$ (nonnegative orthant forward invariant), $f$ of class $C^1$ near the orthant, where $x$ collects a set $\Sigma$ of species (for instance all infected compartments) and $y$ the rest. The boundary face $F_\Sigma = \{x = 0\}$ is *invariant* if $f_x(0,y) = 0$ for all $y \ge 0$; for a chemical-reaction-network representation $f = \Gamma\mathbf{r}$ this holds whenever $\Sigma$ is a *siphon* (every reaction producing a species of $\Sigma$ consumes one). At $(0,y)$ define the transversal and tangential blocks

$$J^\perp(y) = D_xf_x(0,y), \qquad J_{\tan}(y) = D_yf_y(0,y).$$

**Theorem (triangularity).** If $F_\Sigma$ is invariant, then $D_yf_x(0,y) = 0$ on the whole face, so

$$J(0,y) = \begin{pmatrix} J^\perp(y) & 0 \\ * & J_{\tan}(y)\end{pmatrix},$$

the spectrum of $J(0,y)$ is the union of those of $J^\perp(y)$ and $J_{\tan}(y)$, and a fixed point $(0,y^*)$ is linearly asymptotically stable iff both blocks are Hurwitz.

**Proposition (Metzler property).** Under the same hypothesis, $J^\perp(y)$ is a Metzler matrix (nonnegative off-diagonal entries) at every point of the face. Consequently, by Perron–Frobenius, its stability modulus $s(J^\perp)$ is a real eigenvalue, so a boundary fixed point cannot lose stability through a Hopf bifurcation in the directions transversal to its face.

**Corollary (next-generation matrix theorem on siphon faces).** Let $J^\perp(y) = F - V$ be a regular splitting ($V$ invertible, $F \ge 0$, $V^{-1} \ge 0$). Then $J^\perp(y)$ is Hurwitz iff $\rho(FV^{-1}) < 1$; if moreover $V$ is a nonsingular M-matrix, $\operatorname{sign}s(J^\perp(y)) = \operatorname{sign}(\rho(FV^{-1}) - 1)$. Hence a fixed point $(0,y^*)$ with $J_{\tan}(y^*)$ Hurwitz is stable when $\rho(FV^{-1}) < 1$ and unstable when $\rho(FV^{-1}) > 1$ and $V$ is an M-matrix. This holds at any fixed point of an invariant face, not only at a disease-free equilibrium.

## Depends on

- [Unstable mode of the infected subsystem exactly when $R_0 > 1$](../next-generation-matrix-and-the-basic-reproductio/exists-re-pos-iff-one-lt-r0.md)

## Expansion

Invariance means $y \mapsto f_x(0,y)$ vanishes identically, so its $y$-derivative vanishes on the face (by continuity at the boundary too), giving the zero block. For the Metzler property: for $i \ne j$ in $\Sigma$, $(f_x)_i(x,y) \ge 0$ whenever $x_i = 0$ by positivity, and it vanishes on the face, so increasing $x_j$ from $0$ cannot make it negative, i.e. $\partial_{x_j}(f_x)_i(0,y) \ge 0$. For the NGM statement, $-J^\perp = V - F$ is a regular splitting of a Z-matrix; Varga's theorem gives $\rho(V^{-1}F) < 1$ iff $(-J^\perp)^{-1} \ge 0$, and a Z-matrix with nonnegative inverse is a nonsingular M-matrix, i.e. $J^\perp$ is Hurwitz. The sign statement follows by a continuity argument on $tF - V$.

## Sources

- F. Avram, R. Adenane and A.-D. Halanay, "Triangularity of the Jacobian on siphon faces, the Metzler property of its transversal component and other results", arXiv:2603.06778 (2026), Section 3 (theorem on triangularity of the Jacobian on siphon faces, proposition that the transversal block is Metzler, and the NGM corollary for siphon faces), <https://doi.org/10.48550/arXiv.2603.06778>.
- O. Diekmann, J. A. P. Heesterbeek and J. A. J. Metz, "On the definition and the computation of the basic reproduction ratio $R_0$ in models for infectious diseases in heterogeneous populations", Journal of Mathematical Biology 28 (1990), <https://doi.org/10.1007/BF00178324>.
- P. van den Driessche and J. Watmough, "Reproduction numbers and sub-threshold endemic equilibria for compartmental models of disease transmission", Mathematical Biosciences 180 (2002), <https://doi.org/10.1016/S0025-5564(02)00108-6>.
