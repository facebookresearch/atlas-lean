# Large deviations of the Dean–Kawasaki equation with Keller–Segel interaction

**Model.** On the torus $\mathbb T^2$ let $\mathcal G$ be the Green function of the Laplacian and, for $\kappa_1,\kappa_2\in\mathbb R$ and $\mathbb J$ the rotation by $\pi/2$, let
$$\mathcal V[\rho]=-(\kappa_1+\kappa_2\mathbb J)\nabla\mathcal G*\rho,$$
a combination of the Keller–Segel ($\kappa_2=0$; attractive when $-\kappa_1>0$) and Biot–Savart interaction kernels. The Dean–Kawasaki equation describes density fluctuations of $N\sim\varepsilon^{-1}$ interacting Brownian particles:
$$\partial_t\rho^\varepsilon=\Delta\rho^\varepsilon-\nabla\cdot\big(\rho^\varepsilon\mathcal V[\rho^\varepsilon]\big)-\sqrt\varepsilon\,\nabla\cdot\big(\sqrt{\rho^\varepsilon}\circ\xi_K\big),$$
with $\xi_K$ an ultraviolet cutoff of vector-valued space–time white noise (Stratonovich product). Assume the subcritical attraction condition
$$-\kappa_1<\frac{4}{C_{\mathrm{GN}}\|\rho_0\|_{L^1}},$$
with $C_{\mathrm{GN}}$ the optimal Gagliardo–Nirenberg constant in $\|f\|_{L^4}\le C_{\mathrm{GN}}\|\nabla f\|_{L^2}^{1/2}\|f\|_{L^2}^{1/2}+C\|f\|_{L^2}$, and initial data of finite entropy, $\int\rho_0\log\rho_0<\infty$.

**Theorem.**

1. (Existence.) For each $\varepsilon>0$ and cutoff $K$ there is a probabilistically weak, nonnegative renormalized kinetic solution.
2. (Restricted LDP.) Replace $\sqrt\rho$ by smooth approximations $s_\eta$ and let $K(\varepsilon)\to\infty$, $\eta(\varepsilon)\to0$ with $\varepsilon N_{K(\varepsilon)}\to0$ and $\varepsilon N_{K(\varepsilon)}\|s'_{\eta(\varepsilon)}\|_\infty^2$ bounded. Then the laws $\mu^\varepsilon$ of the solutions on $L^1_{[0,T]}L^1(\mathbb T^2)$ satisfy the upper bound $\limsup_{\varepsilon\to0}\varepsilon\log\mu^\varepsilon(F)\le-\inf_F\mathcal I$ for closed $F$ and the restricted lower bound $\liminf_{\varepsilon\to0}\varepsilon\log\mu^\varepsilon(G)\ge-\inf_{G\cap\mathcal C_0}\mathcal I$ for open $G$, where $\mathcal C_0=\bigcup_{p'>2}L^\infty_{[0,T]}W^{1,p'}$ and
$$\mathcal I(\rho)=\sup_{\varphi}\Big\{\langle\rho,\varphi\rangle\big|_0^T-\langle\rho,(\partial_t+\Delta)\varphi\rangle-\langle\rho\mathcal V[\rho],\nabla\varphi\rangle-\tfrac12\langle\rho\nabla\varphi,\nabla\varphi\rangle\Big\}$$
on densities with $\nabla\sqrt\rho\in L^2_{t,x}$ (and $+\infty$ otherwise).

## Expansion

The Keller–Segel kernel is critical in the $L^1$ setting of the equation, since $\nabla\mathcal G\in L^p$ only for $p<2$. The smallness condition lets the entropy dissipation $\int|\nabla\sqrt\rho|^2$ control the aggregation term via Gagliardo–Nirenberg, giving the a priori entropy estimate behind existence and tightness. The rate function is the action of the skeleton equation $\partial_t\rho=\Delta\rho-\nabla\cdot(\rho\mathcal V[\rho])-\nabla\cdot(\sqrt\rho\,g)$ with $L^2$ control $g$; the lower bound is restricted to $\mathcal C_0$ because weak-strong uniqueness of the skeleton equation is only available for such regular paths.

## Sources

- Xiaohao Ji, Yue Sun, Zhengyan Wu, "Dean–Kawasaki Equation with Biot–Savart and Keller–Segel Interactions: Existence and Large Deviations", arXiv:2605.13479 (2026), Theorems 1.2, 1.3 and 3.1, <https://doi.org/10.48550/arXiv.2605.13479>.
