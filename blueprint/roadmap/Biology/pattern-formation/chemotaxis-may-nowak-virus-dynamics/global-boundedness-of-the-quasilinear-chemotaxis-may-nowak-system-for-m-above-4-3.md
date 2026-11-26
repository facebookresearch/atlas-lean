# Global boundedness of the quasilinear chemotaxis–May–Nowak system for $m > 4/3$

**Model.** Let $\Omega \subset \mathbb{R}^n$ be a bounded smooth domain. Uninfected cells $u$, infected cells $v$ and free virus $w$ follow the quasilinear chemotaxis–May–Nowak system
$$
\begin{cases}
u_t = \nabla\cdot\big((1+u)^{m-1}\nabla u\big) - \chi\nabla\cdot(u\nabla v) - u - uw + \varphi, \\
\tau v_t = \Delta v - v + uw, \\
w_t = \Delta w - w + v,
\end{cases}
\qquad x \in \Omega,\ t > 0,
$$
with homogeneous Neumann conditions, $\chi > 0$, $m > 0$, and $\tau \in \{0,1\}$ ($\tau = 0$: parabolic–elliptic–parabolic; $\tau = 1$: fully parabolic). Uninfected cells are attracted to infected ones, infection $uw$ converts $u$ into $v$, and $\varphi \in C^\alpha(\overline\Omega\times[0,\infty))$ with $0 \le \varphi \le \varphi_*$ is the cell supply. Initial data $u_0, w_0 \in W^{2,\infty}(\Omega)$ are nonnegative, not identically zero, with zero normal derivative (and likewise $v_0$ when $\tau = 1$).

**Theorem.** Let $n = 3$ and $m > 4/3$. For $\tau = 0$, and also for $\tau = 1$, every solution with data as above is global and uniformly bounded:
$$ \sup_{t>0}\Big( \|u(\cdot,t)\|_{L^\infty(\Omega)} + \|v(\cdot,t)\|_{W^{1,\infty}(\Omega)} + \|w(\cdot,t)\|_{L^\infty(\Omega)} \Big) < \infty . $$

For $\tau = 0$ the exponent $4/3$ is sharp: finite-time blow-up occurs in balls for $1 < m \le 4/3$.

## Expansion

Total masses of $u$ and $w$ stay bounded because infection removes $u$ at the rate $uw$ and $\varphi$ is bounded. In three dimensions the elliptic (or parabolic) equation for $v$ only gives $v \in L^q$ for $q < 3$ from $uw \in L^1$, so the chemotactic flux must be absorbed by nonlinear diffusion: testing the $u$-equation with $u^{p-1}$, the cross-diffusion term is controlled by $\int u^{p}\,uw$, and time-weighted bounds $\int_0^t e^{s-t}\|w\|_{L^\infty}^b\,ds \le C_b$ together with Gagliardo–Nirenberg interpolation close the $L^p$ estimate exactly when $m > 4/3$. Moser iteration upgrades to $L^\infty$, and the extensibility criterion gives global existence. For $\tau = 1$ maximal Sobolev regularity replaces the elliptic estimate.

## Sources

- Xueli Bai, Fang Li and Suying Liu, "Global Boundedness and Finite-Time Blow-up for a Quasilinear Chemotaxis--May--Nowak System", arXiv:2610.33664 (2026), Section 1, Theorems 1.1 and 1.4; Sections 3 and 6 (proofs), <https://doi.org/10.48550/arXiv.2610.33664>.
