# Quasi-static limit of the Cahn–Hilliard–nutrient tumour model

**Statement.** Consider the Cahn–Hilliard–nutrient tumour system on a bounded $C^2$ domain $\Omega\subset\mathbb{R}^3$ with Dirichlet data,

$$
\begin{aligned}
\partial_t\varphi&=\Delta\mu+(\lambda_p\sigma-\lambda_a)h(\varphi),\\
\mu&=\tfrac{\gamma}{\varepsilon}\Psi'(\varphi)-\gamma\varepsilon\Delta\varphi-\chi\sigma,\\
\kappa\,\partial_t\sigma&=\operatorname{div}\big(D(\varphi)(\nabla\sigma-\eta\nabla\varphi)\big)-\lambda_c\sigma h(\varphi),
\end{aligned}
$$

under the assumptions of [Cahn–Hilliard–nutrient tumour model with Dirichlet boundary data](cahn-hilliard-nutrient-tumour-model-with-dirichlet-boundary-data.md). For each $\kappa\in(0,1]$ let $(\varphi^\kappa,\mu^\kappa,\sigma^\kappa)$ be a weak solution with the same initial data $\varphi_0\in H^1$, $\sigma_0\in L^2$. Then, as $\kappa\to0$ (along a subsequence),

$$
\varphi^\kappa\rightharpoonup^*\varphi_*\ \text{in } L^\infty(0,T;H^1)\cap H^1(0,T;H^{-1}),\qquad \sigma^\kappa\rightharpoonup\sigma_*,\ \mu^\kappa\rightharpoonup\mu_*\ \text{in } L^2(0,T;H^1),\qquad \partial_t(\kappa\sigma^\kappa)\rightharpoonup0\ \text{in }L^2(0,T;H^{-1}),
$$

and $(\varphi_*,\mu_*,\sigma_*)$ is a weak solution of the quasi-static system in which the nutrient equation is replaced by the elliptic equation $0=\operatorname{div}(D(\varphi)(\nabla\sigma-\eta\nabla\varphi))-\lambda_c\sigma h(\varphi)$, $\sigma=\sigma_\infty$ on $\Gamma$. Under the additional hypotheses of the continuous-dependence theorem ($D$ constant, $h$ Lipschitz, $\Psi'$ locally Lipschitz with quartic growth of the constant), weak solutions of the quasi-static system with $\varphi\in L^2(0,T;H^3)$ depend continuously on initial and boundary data and are unique.

## Expansion

The ratio $\kappa/D_0$ compares the nutrient diffusion time-scale with the tumour doubling time; since nutrient diffuses much faster than cells divide, $\kappa\to0$ is the biologically relevant regime. The key is that the energy bound of the parabolic problem has a constant independent of $\kappa$ and its right side stays bounded as $\kappa\to0$; this yields $\kappa$-uniform bounds on $\varphi^\kappa$ in $L^\infty(H^1)$, on $\mu^\kappa,\sigma^\kappa$ in $L^2(H^1)$, and on $\sqrt\kappa\,\sigma^\kappa$ in $L^\infty(L^2)$, so $\kappa\partial_t\sigma^\kappa\to0$ in $L^2(H^{-1})$. Aubin–Lions compactness for $\varphi^\kappa$ handles the nonlinear terms $\Psi'(\varphi)$, $h(\varphi)$ and $D(\varphi)$.

## Depends on

- [Cahn–Hilliard–nutrient tumour model with Dirichlet boundary data](cahn-hilliard-nutrient-tumour-model-with-dirichlet-boundary-data.md)

## Sources

- Harald Garcke, Kei Fong Lam, "Analysis of a Cahn--Hilliard system with non-zero Dirichlet conditions modeling tumor growth with chemotaxis", arXiv:1604.00287: Section 2: Definition 2.5, Theorem 2.6 (quasi-static limit) and Theorem 2.7 (continuous dependence for the quasi-static system); proofs in Section 4. <https://doi.org/10.48550/arXiv.1604.00287>
