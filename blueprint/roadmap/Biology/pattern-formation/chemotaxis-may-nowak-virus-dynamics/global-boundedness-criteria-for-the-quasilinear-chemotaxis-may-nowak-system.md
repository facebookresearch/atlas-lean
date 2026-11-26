# Global boundedness criteria for the quasilinear chemotaxis-May-Nowak system

**Model.** Spatial within-host virus dynamics extend the May-Nowak model: uninfected cells $u$, infected cells $v$ and free virions $w$ on a smooth bounded domain $\Omega \subset \mathbb{R}^n$, $n \ge 2$, with Neumann boundary conditions,

$$u_t = \nabla\cdot(D(u)\nabla u) - \chi\nabla\cdot(u\nabla v) - u - uw + \varphi(x,t), \qquad \kappa v_t = \Delta v - v + uw, \qquad w_t = \Delta w - w + v.$$

Uninfected cells move toward infected cells (taxis sensitivity $\chi > 0$), $\varphi \ge 0$ is a bounded supply of uninfected cells, and the diffusion satisfies $D \in C^2([0,\infty))$, $D > 0$, $D(s) \ge k_Ds^{m-1}$. $\kappa = 0$ gives the parabolic-elliptic-parabolic system, $\kappa = 1$ the fully parabolic one. Initial data are nonnegative, nontrivial, in $W^{2,\infty}(\Omega)$ and compatible with the boundary condition.

**Theorem.**
1. ($\kappa = 0$) If
$$m > 1 + \frac{n}{4}\ (n \ge 4), \qquad m > 3 - \frac{4}{n}\ (n \in \{2,3\}),$$
the solution is global and $\|u(\cdot,t)\|_{L^\infty} + \|v(\cdot,t)\|_{W^{1,\infty}} + \|w(\cdot,t)\|_{L^\infty} \le C$ for all $t > 0$.
2. ($\kappa = 1$) If $n \ge 4$ and $m > 1 + \frac{n}{4}$, the same global boundedness holds.

In $n = 2$ with $\kappa = 0$, every $m > 1$ gives $L^p$ bounds on $u$ for all $p$.

## Expansion

The difficulty is the infection source $uw$, which feeds the attractant $v$ and is not controlled by mass alone. Weighted space-time estimates of $uw$ give low-order $L^q$ bounds for the virions $w$, which start a bootstrap for $\|u\|_{L^p}$. In the $L^p$ testing of the $u$-equation, the chemotactic term $\chi\int u^{p-1}\nabla u\cdot\nabla v$ becomes, after integration by parts, an integral involving $u^p\,uw$ (for $\kappa = 0$, $-\Delta v = uw - v$); keeping this product structure in the Gagliardo-Nirenberg interpolation lets the diffusion $\int u^{m+p-3}|\nabla u|^2$ absorb it under the stated exponent conditions, improving earlier sufficient conditions. Moser-type iteration then gives $L^\infty$ bounds.

## Sources

- Xueli Bai, Fang Li, Suying Liu and Xuxuan Luo, "Improved Global Boundedness Criteria via Refined Bootstrap Estimates for a Quasilinear Chemotaxis-May-Nowak System", arXiv:2610.33657 (2026), Section 1, Theorems 1.1 and 1.2, Section 3, Propositions 3.2-3.4, <https://doi.org/10.48550/arXiv.2610.33657>.
