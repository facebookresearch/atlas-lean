# Turing instability of the nonlocal Staver–Levin model with resource limitation

**Model.** Let $G, S, T, F \ge 0$ be the local proportions of grass, savanna saplings, savanna trees and forest trees at $x \in \mathbb R$, with $G + S + T + F = 1$. Fire spreads from burning grass with kernel $w$; forest and savanna seeds disperse with kernels $J_F, J_T$. The spatial Staver–Levin model is

$$\begin{aligned}
\partial_t G &= \mu S + \nu T + \phi(w * G)F - \alpha G(J_F * F) - \beta G(J_T * T),\\
\partial_t S &= -\mu S - \omega(w * G)S - \alpha S(J_F * F) + \beta G(J_T * T),\\
\partial_t T &= -\nu T + \omega(w * G)S - \alpha T(J_F * F),\\
\partial_t F &= \alpha(G + S + T)(J_F * F) - \phi(w * G)F,
\end{aligned}$$

where the kernels are even probability densities (H1–H2), and the fire responses $\omega$ (sapling recruitment) and $\phi$ (forest mortality) are step functions of flammable cover with thresholds $\theta_1, \theta_2 \in (0,1)$ (H3). With resource limitation on forest growth with competition kernel $R$ and constraint $r \in (0,1]$, the grass–forest subsystem ($F = 1 - G$) reduces to

$$\partial_t G = (1 - G)\,\phi(w * G) - \alpha G\big(1 - J_F * G\big)\Big(1 - \tfrac1r + \tfrac1r R * G\Big).$$

**Theorem.**
1. (No patterns from fire alone) Every locally asymptotically stable equilibrium of the non-spatial Staver–Levin model is a locally asymptotically stable homogeneous equilibrium of the spatial model, for all kernels satisfying (H1–H2) and fire responses satisfying (H3).
2. (All-grass state) With resource limitation and positive definite kernels (non-negative Fourier transforms, e.g. kernels maximal at $0$), a stable all-grass state of the non-spatial model remains stable in the spatial model.
3. (Mixed states) For a mixed equilibrium $\bar G \in (0,1)$ the dispersion relation is

$$\lambda(\xi) = A\,\hat w(|\xi|) + B\,\hat R(|\xi|) + C\,\hat J_F(|\xi|) + D,$$

with $A = \phi'(\bar G)(1 - \bar G)$ ($= 0$ almost everywhere under (H3)), $B = -\tfrac{\alpha}{r}\bar G(1 - \bar G) < 0$ from resource competition, $C > 0$ from seed dispersal and $D = \lim_{|\xi|\to\infty}\lambda(\xi)$. A Turing instability occurs iff $\lambda(0) = A + B + C + D < 0$, $D < 0$, and $\lambda(\xi) > 0$ for some $\xi \ne 0$. Where $A = 0$ the last condition reads $|B|\big(1 - \hat R(|\xi|)\big) - C\big(1 - \hat J_F(|\xi|)\big) > -\lambda(0)$ for some $\xi \ne 0$: the loss of competition at that wave number must outweigh the loss of dispersal by more than the margin $-\lambda(0)$. This can hold even with $1 - \hat R < 1 - \hat J_F$ when $|B|/C$ is large, so it does not require competition to act over longer distances than seed dispersal.

## Expansion

Linearizing at a homogeneous state and taking Fourier transforms replaces each convolution by multiplication with $\hat J(\xi)$, where $\hat J(0) = 1$, $|\hat J(\xi)| \le 1$, $\hat J$ is even and $\hat J(\xi) \to 0$ (Riemann–Lebesgue). With step-function fire responses the derivatives of $\phi, \omega$ vanish, so fire enters the linearization only through its level, and every Fourier mode has growth rates dominated by those of the $\xi = 0$ mode; this gives parts 1–2. In part 3 the only destabilizing contribution is the reduction of the competition term $B\hat R(\xi)$ relative to the stabilizing dispersal term $C\hat J_F(\xi)$ at non-zero wave numbers. Numerical continuation shows these pattern-forming bifurcations are subcritical, so stable heterogeneous savanna–forest mosaics appear before the homogeneous state loses stability, with hysteresis; patterns persist over a range of relative length scales of seed dispersal and competition.

## Sources

- D. Patterson, S. Levin, A. C. Staver, J. Touboul, "Pattern formation in mesic savannas", Bulletin of Mathematical Biology 86 (2023) 3, Eqs. (2)–(10), hypotheses (H1)–(H4), Definition 1 and Propositions 1–3 (calculations in Appendices A.1–A.2), <https://doi.org/10.1007/s11538-023-01231-7>, PMCID PMC10682166.
