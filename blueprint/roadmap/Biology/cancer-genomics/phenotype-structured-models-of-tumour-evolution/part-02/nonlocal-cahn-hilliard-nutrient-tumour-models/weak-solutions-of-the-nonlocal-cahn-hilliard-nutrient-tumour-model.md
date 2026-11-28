# Weak solutions of the nonlocal Cahn–Hilliard–nutrient tumour model

Let $\Omega\subset\mathbb{R}^3$ be bounded, $T>0$, and let $\varphi$ denote the tumour–healthy cell order parameter (pure phases $\varphi=\pm1$) and $\sigma$ the nutrient concentration. Replacing the Ginzburg–Landau gradient energy of the Hawkins-Daarud four-species tumour model by a nonlocal interaction kernel $J$ gives

$$
\begin{aligned}
\varphi_t&=\operatorname{div}\big(m(\varphi)\nabla\mu\big)+P(\varphi)\big(\sigma+\chi(1-\varphi)-\mu\big),\\
\mu&=A\Psi'(\varphi)+Ba\varphi-BJ\star\varphi-\chi\sigma,\\
\sigma_t&=\operatorname{div}\big(n(\varphi)\nabla(\sigma+\chi(1-\varphi))\big)-P(\varphi)\big(\sigma+\chi(1-\varphi)-\mu\big),
\end{aligned}
$$

with $a(x)=\int_\Omega J(x-y)\,dy$, $(J\star\varphi)(x)=\int_\Omega J(x-y)\varphi(y)\,dy$, homogeneous Neumann conditions for $\varphi,\mu,\sigma$, constants $A,B>0$ and chemotaxis parameter $\chi\ge0$. The associated free energy is

$$
E(\varphi,\sigma)=\int_\Omega A\Psi(\varphi)+\tfrac B2a|\varphi|^2-\tfrac B2\varphi\,(J\star\varphi)+\tfrac12|\sigma|^2+\chi\sigma(1-\varphi)\,dx .
$$

**Existence (non-degenerate case).** Assume: $m,n$ continuous with $0<m_1\le m\le m_2$, $0<n_1\le n\le n_2$; $J\in W^{1,1}_{loc}$ symmetric with $a\ge0$ and $\sup_x\int_\Omega|J(x-y)|dy$, $\sup_x\int_\Omega|\nabla J(x-y)|dy$ finite; $\Psi\in C^2$ with $A\Psi''+Ba\ge c_0>\chi^2$, at least quadratic growth $\Psi(s)\ge c_2|s|^2-c_1$ for a suitably large $c_2$, and $|\Psi'|^z\le c_3\Psi+c_4$ for some $z\in(1,2]$; $P$ continuous with $0\le P(s)\le c_5(1+|s|^q)$, $q\in[1,10/3)$; and $\varphi_0,\sigma_0\in L^2$ with $\Psi(\varphi_0)\in L^1$. Then a weak solution exists on $[0,T]$ satisfying, for all $t>0$, the energy inequality

$$
E(\varphi(t),\sigma(t))+\int_0^t\!\!\int_\Omega m(\varphi)|\nabla\mu|^2+n(\varphi)|\nabla(\sigma+\chi(1-\varphi))|^2+P(\varphi)\big(\sigma+\chi(1-\varphi)-\mu\big)^2\le E(\varphi_0,\sigma_0).
$$

If $q\le4/3$, then $\varphi_t,\sigma_t\in L^2(0,T;(H^1)')$, $\varphi,\sigma\in C([0,T];L^2)$ and the energy inequality is an equality.

**Continuous dependence.** If $m=n=1$, $P$ is bounded and Lipschitz, and $\Psi'$ satisfies $|\Psi'(s_1)-\Psi'(s_2)|\le c_6(1+|s_1|^r+|s_2|^r)|s_1-s_2|$ with $r\in[0,4/3]$, then any two weak solutions satisfy

$$
\|\varphi_1(t)-\varphi_2(t)\|_{(H^1)'}^2+\|\sigma_1(t)-\sigma_2(t)\|_{(H^1)'}^2+\int_0^t\|\varphi_1-\varphi_2\|_{L^2}^2+\|\sigma_1-\sigma_2\|_{L^2}^2\le C\big(\|\varphi_{1,0}-\varphi_{2,0}\|_{(H^1)'}^2+\|\sigma_{1,0}-\sigma_{2,0}\|_{(H^1)'}^2\big),
$$

so weak solutions are unique; if $r\le2/3$ the chemical potentials also depend continuously on the data in $L^2(0,t;(H^1)')$.

## Expansion

The nonlocal energy models cell–cell adhesion through the kernel $J$; the source terms $P(\varphi)(\sigma+\chi(1-\varphi)-\mu)$ are chosen so that the energy is nonincreasing, giving the a priori estimate behind existence (Faedo–Galerkin approximation and compactness). The condition $c_0>\chi^2$ makes the convexity of $A\Psi+Ba|\cdot|^2/2$ dominate the chemotactic cross term in the energy. Compared with the local model, the nonlocal operator gives weaker spatial regularity of $\varphi$, which is why $P$ is limited to growth below order $10/3$. Continuous dependence is proved in the dual space $(H^1)'$ by testing the difference equations with the inverse Neumann Laplacian.

## Sources

- S. Frigeri, K. F. Lam, E. Rocca, "On a diffuse interface model for tumour growth with non-local interactions and degenerate mobilities", Section 2 (Theorems 2.1 and 2.2). <https://doi.org/10.48550/arXiv.1703.03553>
