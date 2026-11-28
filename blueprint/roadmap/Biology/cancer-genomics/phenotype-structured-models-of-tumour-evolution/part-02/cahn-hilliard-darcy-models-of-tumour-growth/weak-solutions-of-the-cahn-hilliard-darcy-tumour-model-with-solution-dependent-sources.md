# Weak solutions of the Cahn–Hilliard–Darcy tumour model with solution-dependent sources

**Setting.** Let $\Omega\subset\mathbb R^d$, $d\in\{2,3\}$, be a bounded $C^3$ domain, $Q=\Omega\times(0,T)$, $\Sigma=\partial\Omega\times(0,T)$. A tumour–host mixture is described by the phase difference $\varphi$ ($\varphi=1$ tumour, $\varphi=-1$ host), chemical potential $\mu$, nutrient $\sigma$, mixture velocity $\vec v$ and pressure:

$$\operatorname{div}\vec v=\Gamma_{\vec v}(\varphi,\sigma),\qquad \partial_t\varphi+\operatorname{div}(\varphi\vec v)=\operatorname{div}(m(\varphi)\nabla\mu)+\Gamma_\varphi(\varphi,\sigma),$$

$$\mu=A\Psi'(\varphi)-B\Delta\varphi-\chi\sigma,\qquad 0=\Delta\sigma-h(\varphi)\sigma,$$

with $\partial_n\varphi=0$, $\sigma=1$ on $\Sigma$ and $\varphi(0)=\varphi_0\in H^1$. Darcy's law is closed in one of three ways ($K,a>0$, $g\in L^2(\Sigma)$):

- (Dirichlet) $\vec v=-K(\nabla q+\varphi\nabla(\mu+\chi\sigma))$, $q=0$ and $m(\varphi)\partial_n\mu=\varphi\vec v\cdot\vec n$ on $\Sigma$;
- (Robin) $\vec v=-K(\nabla p-(\mu+\chi\sigma)\nabla\varphi)$, $\mu=0$ and $K\partial_np=a(g-p)$ on $\Sigma$;
- (Neumann) the same Darcy law with $\partial_n\mu=0$ and $K\partial_np=a(g-p)$ on $\Sigma$.

**Hypotheses.** The mobility satisfies $0<m_0\le m\le m_1$; $0\le h\le1$ is continuous; $\Psi\in C^2$ is non-negative with $\Psi(s)\ge C_1|s|^2-C_2$, $|\Psi''(s)|\le C_3(1+|s|^r)$ for some $r\in[0,2]$, and $|\Psi'(s)|\le C_4(1+\Psi(s))$. The sources are affine in the nutrient,

$$\Gamma_{\vec v}(\varphi,\sigma)=b_{\vec v}(\varphi)\sigma+f_{\vec v}(\varphi),\qquad \Gamma_\varphi(\varphi,\sigma)=b_\varphi(\varphi)\sigma+f_\varphi(\varphi),$$

with $b_{\vec v},b_\varphi,f_{\vec v},f_\varphi$ bounded and continuous, so the mass sources may depend on the solution.

**Theorem.** Under these hypotheses there exists a weak solution, in the sense of the source's Definitions 2.1 (Dirichlet) and 2.2 (Robin), for the Dirichlet and for the Robin closures; for the Neumann closure one exists in the sense of Definition 2.3 provided the potential has at most quadratic growth, $|\Psi''|\le C_3$. In every case

$$\varphi\in L^\infty(0,T;H^1)\cap L^2(0,T;H^3),\qquad \vec v\in L^2(Q),\qquad 0\le\sigma\le1,\qquad \sigma-1\in L^2(0,T;H^1_0),$$

and, closure by closure (with $H^{-1}$ the dual of $H^1_0$):

- Dirichlet: $\varphi\in W^{1,8/5}(0,T;(H^1)^*)$, $\mu\in L^2(0,T;H^1)$, $q\in L^{8/5}(0,T;H^1_0)$;
- Robin: $\varphi\in W^{1,8/5}(0,T;H^{-1})$, $\mu\in L^2(0,T;H^1_0)$, $p\in L^{8/5}(0,T;H^1)$ with $p|_\Sigma\in L^2(\Sigma)$;
- Neumann: $\varphi\in W^{1,8/5}(0,T;(H^1)^*)$, $\mu\in L^2(0,T;H^1)$, $p\in L^{8/5}(0,T;H^1)$ with $p|_\Sigma\in L^2(\Sigma)$.

## Expansion

The quasi-static nutrient equation is regularized by $\theta\,\partial_t\sigma$ and the problem is solved by a Galerkin scheme; the maximum principle gives $0\le\sigma\le1$. The key a priori estimate tests the $\varphi$-equation with $\mu$ and the $\mu$-equation with $\partial_t\varphi$; with solution-dependent sources the convective and source contributions do not cancel, and the boundary conditions on the pressure are chosen so that the Darcy terms can be controlled by the Ginzburg–Landau energy $\int A\Psi(\varphi)+\tfrac B2|\nabla\varphi|^2$ through elliptic estimates for the pressure. Compactness in $\theta\to0$ (Aubin–Lions, with the $W^{1,8/5}$ time regularity coming from the $L^{8/5}$ bound on $\varphi\vec v$ in three dimensions) passes to the limit in the nonlinear terms.

## Sources

- Harald Garcke, Kei Fong Lam, "On a Cahn–Hilliard–Darcy system for tumour growth with solution dependent source terms", arXiv:1611.00234 (2016), system (1.1) with Darcy closures (1.2), Assumption 2.1, Definitions 2.1–2.3 and Theorems 2.1–2.3, <https://doi.org/10.48550/arXiv.1611.00234>.
