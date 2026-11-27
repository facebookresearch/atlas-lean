# Stochastic Cahn-Hilliard tumor model with chemotaxis and variable mobility

**Model.** In a bounded domain $D\subset\mathbb R^3$, let $\phi\in[0,1]$ be the tumor volume fraction (diffuse interface between tumor $\{\phi=1\}$ and healthy tissue $\{\phi=0\}$) and $\sigma$ the nutrient concentration. With a double-well potential $\Psi$, interface width $\varepsilon$, chemotaxis coefficient $\chi\ge0$, mobilities $m_1(\phi),m_2(\sigma)$, proliferation $\beta\sigma f(\phi)$, apoptosis $\alpha f(\phi)$ and nutrient consumption $\delta\sigma f(\phi)$, the stochastic system is

$$d\phi=\operatorname{div}\big(m_1(\phi)(\nabla\mu-\chi\nabla\sigma)\big)dt+(\beta\sigma-\alpha)f(\phi)\,dt+G_1(\phi)\,dW_1,\qquad \mu=\Psi'(\phi)-\varepsilon^2\Delta\phi,$$

$$d\sigma=\operatorname{div}\big(m_2(\sigma)(\nabla\sigma-\chi\nabla\phi)\big)dt-\delta\sigma f(\phi)\,dt+G_2(\sigma)\,dW_2,$$

with independent cylindrical Wiener processes $W_1,W_2$ on separable Hilbert spaces $U_1,U_2$ (orthonormal bases $(u_k)$), noise operators $G_1,G_2$, and homogeneous Neumann conditions. Write $H=L^2(D)$, $V=H^1(D)$ and $V_2=\{v\in H^2(D):\partial_nv=0\}$. The deterministic part derives from a Ginzburg-Landau energy with chemotactic coupling; multiplicative noise accounts for unpredictable growth (for example metastatic activation or angiogenic supply) and therapy uncertainty.

**Theorem (existence of martingale solutions).** Assume

- (A1) $\alpha,\beta,\delta,\chi\ge0$ and $\varepsilon>0$ are fixed;
- (A2) $f\in C^{0,1}(\mathbb R;[0,1])$;
- (A3) $m_1,m_2\in C^0(\mathbb R;[m_0,m_\infty])$ with $0<m_0\le m_\infty<\infty$;
- (A4) $\Psi\in C^2(\mathbb R;\mathbb R_{\ge0})$, $\Psi'(0)=0$, and for some $C_\Psi>0$ and all $x$, $|\Psi'(x)|^q+|\Psi''(x)|\le C_\Psi(1+|\Psi(x)|)$ and $\Psi''(x)\ge-C_\Psi$, where $q>1$ if $\chi=0$ or $m_1$ is constant, and $q=2$ if $\chi>0$ and $m_1$ is non-constant;
- (A5) for $i\in\{1,2\}$, $G_i:H\to\mathcal L^2(U_i,H)$ is measurable and $G_i(v)u_k=g_{i,k}(v)$ for all $v\in H$, $k\in\mathbb N$, for functions $g_{i,k}\in W^{1,\infty}(\mathbb R)$ with $\sum_k\|g_{i,k}\|^2_{W^{1,\infty}(\mathbb R)}<\infty$;
- (A6) $\phi_0\in V$ with $\Psi(\phi_0)\in L^1(D)$, and $\sigma_0\in H$.

Then there is a probabilistically weak (martingale) solution with $\phi\in L^\ell(\Omega;C^0([0,T];H))\cap L^{\ell/2}(\Omega;L^2(0,T;V_2))$, $\mu\in L^{\ell/2}(\Omega;L^2(0,T;V))$, $\sigma\in L^\ell(\Omega;C^0([0,T];H))\cap L^{\ell/2}(\Omega;L^2(0,T;V))$ for every $\ell\ge2$, satisfying the energy inequality

$$\mathbb E\sup_s\|\phi\|_V^2+\mathbb E\sup_s\|\Psi(\phi)\|_{L^1}+\mathbb E\|\nabla\mu\|_{L^2(H)}^2+\mathbb E\sup_s\|\sigma\|_H^2+\mathbb E\|\sigma\|^2_{L^2(V)}\le c\big(\|\phi_0\|_V^2+\|\Psi(\phi_0)\|_{L^1}+\|\sigma_0\|_H^2\big).$$

This is the first such result for stochastic tumor models with non-constant mobilities.

**Theorem (strong well-posedness).** If the mobilities are constant and $|\Psi''|^2\le C(1+|\Psi|)$ (for example the quartic double well), pathwise uniqueness holds, so the system has a unique probabilistically strong solution on the original probability space, with the same regularity and energy bound, and solutions depend continuously on the initial data up to a sequence of stopping times.

## Expansion

Monotone-operator theory does not apply because of the non-constant mobilities and the coupling between the Cahn-Hilliard and reaction-diffusion equations, so the proof uses a two-level approximation: a Galerkin projection in space and a Yosida-type regularization of $\Psi'$. Uniform energy estimates follow from Itô's formula for the Ginzburg-Landau energy plus the nutrient $L^2$ norm, with the chemotactic cross terms absorbed using the potential's growth, and with Burkholder-Davis-Gundy controlling the stochastic integrals. Tightness of the laws, Prokhorov and Skorokhod theorems, and identification of the limit martingale give a martingale solution. With constant mobilities, pathwise uniqueness, obtained via stopping-time localization because $\Psi'$ is not globally Lipschitz, upgrades it to a strong solution by Yamada-Watanabe. Numerical simulations with a finite-element scheme show how increasing noise intensity changes tumor aggregation and nutrient consumption.

## Sources

- M. Fritz, L. Scarpa, "Analysis and computations of a stochastic Cahn-Hilliard model for tumor growth with chemotaxis and variable mobility", *Stochastics and Partial Differential Equations: Analysis and Computations* 13(2) (2025), 1051–1096, Introduction (deterministic and stochastic models), Assumption 3.1 (A1)–(A6), theorem "Existence of martingale solutions" (main result), theorem "Strong well-posedness", and numerical section, <https://doi.org/10.1007/s40072-025-00348-1> (preprint arXiv:2312.06288).
