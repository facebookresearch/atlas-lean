# Well-posedness of the Caputo time-fractional SIR system with $p$-Laplacian diffusion

Let $\Omega \subset \mathbb{R}^n$ be a bounded domain with smooth boundary, $\mathcal{T} > 0$, $0 < \alpha < 1$, $p \ge 2$, and let ${}^{C}D^{\alpha}_t$ denote the Caputo derivative

$$
{}^{C}D^{\alpha}_t f(t) = \frac{1}{\Gamma(1-\alpha)} \int_0^t (t-y)^{-\alpha} f'(y)\, dy .
$$

For diffusion coefficients $\lambda_1, \lambda_2, \lambda_3 > 0$, recruitment $\beta N$, transmission rate $\mu$, natural death rate $\xi$, recovery rate $\kappa$ and a vaccination control $u(x,t) \in [0,1]$, consider on $\Omega_{\mathcal{T}} = \Omega \times [0,\mathcal{T}]$

$$
\begin{aligned}
{}^{C}D^{\alpha}_t S &= \lambda_1 \Delta_p S + \beta N - \mu S I - \xi S - u S, \\
{}^{C}D^{\alpha}_t I &= \lambda_2 \Delta_p I + \mu S I - (\xi + \kappa) I, \\
{}^{C}D^{\alpha}_t R &= \lambda_3 \Delta_p R + \kappa I - \xi R + u S,
\end{aligned}
$$

where $\Delta_p v = \nabla \cdot (|\nabla v|^{p-2} \nabla v)$, with homogeneous Neumann conditions $\nabla S \cdot \vec n = \nabla I \cdot \vec n = \nabla R \cdot \vec n = 0$ on $\partial\Omega \times [0,\mathcal{T}]$ and initial data $(S_0, I_0, R_0)$. Write $\nu = (S,I,R)$, $\mathcal{H} = (L^2(\Omega))^3$ and $\mathcal{W} = (W^{1,p}(\Omega))^3$ (no boundary values are imposed, matching the Neumann problem); a weak solution satisfies $\langle {}^{C}D^{\alpha}_t \nu, \varphi\rangle + \langle \mathcal{L}\nu, \varphi\rangle - \langle \Psi(\nu), \varphi\rangle = 0$ for all $\varphi \in L^p(0,\mathcal{T};\mathcal{W})$, where $\mathcal{L}\nu = -\lambda \Delta_p \nu$ and $\Psi$ collects the reaction terms. The source writes $W^{1,p}_0(\Omega)$ here, which would impose zero boundary values, i.e. a Dirichlet problem, inconsistent with its Neumann conditions; the page states the Neumann problem throughout.

**Theorem.**

1. For $\nu^0 \in L^2(\Omega)^3$ there exists a weak solution in $L^\infty(0,\mathcal{T};\mathcal{H}) \cap L^p(0,\mathcal{T};\mathcal{W})$.
2. The weak solution is unique.
3. For positive initial data the solution is positive.

## Expansion

Existence is proved by the Faedo–Galerkin method: project onto finite-dimensional subspaces, obtain a priori bounds from the fractional energy inequality $({}^{C}D^{\alpha}_t \varphi, \varphi)_{L^2} \ge \tfrac12\, {}^{C}D^{\alpha}_t \|\varphi\|_{L^2}^2$ (Alikhanov's lemma) together with the monotonicity of $-\Delta_p$, and pass to the limit using compactness and the Minty trick for the monotone operator. Uniqueness follows by testing the difference of two solutions against itself, using the strict monotonicity of the $p$-Laplacian and a fractional Gronwall argument. Positivity follows by testing with negative parts of the components.

## Sources

- Achraf Zinihi, Moulay Rchid Sidi Ammi, Delfim F. M. Torres, "Fractional differential equations of a reaction-diffusion SIR model involving the Caputo-fractional time-derivative and a nonlinear diffusion operator", Evolution Equations and Control Theory 14 (2025), 944–967, <https://doi.org/10.3934/eect.2025018>. Published version of arXiv:2502.00509, cited next; locators there refer to the arXiv version.
- Achraf Zinihi, Moulay Rchid Sidi Ammi, Delfim F. M. Torres, "Fractional differential equations of a reaction-diffusion SIR model involving the Caputo-fractional time-derivative and a nonlinear diffusion operator", arXiv (2025). Definition 2.2, Lemma 2.5, Definition 4.1, Theorem 4.3, Theorem 4.4, Theorem 4.5. <https://doi.org/10.48550/arXiv.2502.00509>
