# Cahn–Hilliard–nutrient tumour model with Dirichlet boundary data

**Model.** Let $\Omega\subset\mathbb{R}^3$ be bounded with $C^2$ boundary $\Gamma$ and $T>0$. The order parameter $\varphi$ ($\varphi=1$ tumour, $\varphi=-1$ healthy tissue), chemical potential $\mu$ and nutrient concentration $\sigma$ satisfy

$$
\begin{aligned}
\partial_t\varphi&=\Delta\mu+(\lambda_p\sigma-\lambda_a)h(\varphi),\\
\mu&=\tfrac{\gamma}{\varepsilon}\Psi'(\varphi)-\gamma\varepsilon\Delta\varphi-\chi\sigma,\\
\kappa\,\partial_t\sigma&=\operatorname{div}\big(D(\varphi)(\nabla\sigma-\eta\nabla\varphi)\big)-\lambda_c\sigma h(\varphi),
\end{aligned}
$$

in $\Omega\times(0,T)$, with Dirichlet data $\varphi=-1$, $\mu=\mu_\infty$, $\sigma=\sigma_\infty$ on $\Gamma\times(0,T)$ and initial data $\varphi_0,\sigma_0$. Here $\lambda_p,\lambda_a,\lambda_c$ are proliferation, apoptosis and consumption rates, $\chi\ge0$ is the chemotaxis and $\eta\ge0$ the active-transport coefficient, $\varepsilon,\gamma,\kappa>0$, and $h$ interpolates $h(-1)=0$, $h(1)=1$.

**Assumptions.** $D,h\in C^0\cap L^\infty(\mathbb{R})$ with $0<D_0\le D\le D_1$ and $0\le h\le h_\infty$; $\Psi\ge0$ is $C^1$, a convex function plus a quadratic perturbation with bounded second derivative, and $|\Psi'(y)|^s\le k_1(1+\Psi(y))$ for some $s\in(1,2]$; $\varphi_0\in H^1$, $\sigma_0\in L^2$, $\Psi(\varphi_0)\in L^1$, and $\mu_\infty,\sigma_\infty\in L^2(0,T;H^1)\cap H^1(0,T;L^2)$.

**Theorem (existence and energy bound).** Under these assumptions there is a weak solution with $\varphi\in(-1+L^\infty(0,T;H^1_0))\cap H^1(0,T;H^{-1})$, $\mu\in\mu_\infty+L^2(0,T;H^1_0)$, $\sigma\in(\sigma_\infty+L^2(0,T;H^1_0))\cap H^1(0,T;H^{-1})$, and

$$
\sup_{s\in(0,T]}\Big(\|\Psi(\varphi(s))\|_{L^1}+\|\varphi(s)\|_{H^1}^2+\kappa\|\sigma(s)\|_{L^2}^2\Big)+\|\mu\|_{L^2(H^1)}^2+\|\sigma\|_{L^2(H^1)}^2\le C\Big(1+\kappa\|\sigma_0-\sigma_\infty(0)\|_{L^2}^2+\kappa^2\|\partial_t\sigma_\infty\|_{L^2(L^2)}^2+\kappa\|\sigma_\infty\|_{L^\infty(L^2)}^2\Big)
$$

with $C$ independent of $\kappa$.

**Theorem (continuous dependence).** If moreover $D\equiv D_0$, $h$ is Lipschitz and $|\Psi'(s_1)-\Psi'(s_2)|\le k_3(1+|s_1|^4+|s_2|^4)|s_1-s_2|$, then any two weak solutions with $\varphi_i\in L^2(0,T;H^3)$ and $\sigma_i\in L^\infty(0,T;L^2)$ satisfy a stability estimate bounding $\sup_t(\|\varphi_1-\varphi_2\|_{L^2}^2+\kappa\|\sigma_1-\sigma_2\|_{L^2}^2)$ plus the $L^2(0,T)$ norms of $\mu_1-\mu_2$ in $L^2$ and of $\sigma_1-\sigma_2$, $\varphi_1-\varphi_2$ in $H^1$, by a constant times the differences of initial data and of Dirichlet data. In particular the weak solution is unique in this class.

## Expansion

Existence is by Galerkin approximation. Testing the three equations with $\mu-\mu_\infty$, $\partial_t\varphi$ and $\sigma-\sigma_\infty$ gives an energy identity in which the source terms $(\lambda_p\sigma-\lambda_a)h(\varphi)$ are controlled because $h$ is bounded; the Dirichlet condition $\varphi=-1$ supplies a Poincaré inequality for $\varphi+1$, so no mass constraint is needed, which is the main analytic difference from the Neumann problem. The growth condition on $\Psi'$ bounds the mean of $\mu$ that would otherwise be uncontrolled. Uniqueness follows by subtracting two solutions and using the polynomial bound on $\Psi''$ with the $H^3$ regularity of $\varphi_i$.

## Sources

- Harald Garcke, Kei Fong Lam, "Analysis of a Cahn--Hilliard system with non-zero Dirichlet conditions modeling tumor growth with chemotaxis", arXiv:1604.00287: Section 2: Assumption 1, Definition 2.1, Theorem 2.2 (existence and energy inequality), Assumption 2 and Theorem 2.4 (continuous dependence). <https://doi.org/10.48550/arXiv.1604.00287>
