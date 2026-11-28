# Fluctuation SPDE for the SIR model on a refining spatial grid

**Model.** On the grid $D_\varepsilon=\{x_1,\dots,x_\ell\}$, $\ell=\varepsilon^{-1}$, of the circle $\mathbb{T}=[0,1)$, a stochastic SIR model with total population of order $\mathbf{N}$ tracks the rescaled numbers $S_{\mathbf{N},\varepsilon},I_{\mathbf{N},\varepsilon},R_{\mathbf{N},\varepsilon}$ at each site: infections occur at rate $\mathbf{N}\beta(x_i)SI/(S+I+R)$, recoveries at rate $\mathbf{N}\alpha(x_i)I$, and each compartment $J\in\{S,I,R\}$ migrates to each neighbour at rate $\mathbf{N}\mu_J\varepsilon^{-2}J$, all driven by independent Poisson processes; $\beta,\alpha$ are continuous, periodic and nonnegative. As $\mathbf{N}\to\infty$ the model converges to the lattice ODE $\dot Z_\varepsilon=b_\varepsilon(Z_\varepsilon)$ with discrete Laplacian $\Delta_\varepsilon$, and as $\varepsilon\to 0$ that ODE converges uniformly to the reaction-diffusion system

$$\partial_t\mathbf{s}=\mu_S\Delta\mathbf{s}-\frac{\beta\,\mathbf{s}\mathbf{i}}{\mathbf{a}},\quad \partial_t\mathbf{i}=\mu_I\Delta\mathbf{i}+\frac{\beta\,\mathbf{s}\mathbf{i}}{\mathbf{a}}-\alpha\mathbf{i},\quad \partial_t\mathbf{r}=\mu_R\Delta\mathbf{r}+\alpha\mathbf{i},\qquad \mathbf{a}=\mathbf{s}+\mathbf{i}+\mathbf{r}.$$

**Statements.**

1. *(CLT at fixed mesh.)* If $\sqrt{\mathbf{N}}\,(Z_{\mathbf{N},\varepsilon}(0)-Z_\varepsilon(0))\to 0$, then $\Psi_{\mathbf{N},\varepsilon}=\sqrt{\mathbf{N}}\,(Z_{\mathbf{N},\varepsilon}-Z_\varepsilon)$ converges locally uniformly in law, as $\mathbf{N}\to\infty$, to the Gaussian diffusion $\Psi_\varepsilon(t)=\int_0^t\nabla_z b_\varepsilon(Z_\varepsilon(r))\Psi_\varepsilon(r)\,dr+\mathcal{M}_\varepsilon(t)$, with $\mathcal{M}_\varepsilon$ a Gaussian martingale whose covariance is $\sum_j h_jh_j^{\top}\beta_j(Z_\varepsilon)$ over the jump directions $h_j$.
2. *(Functional CLT as $\varepsilon\to0$.)* Assume in addition (Assumptions 1.1, 1.2 and 2.1 of the source) that $\mathbf{s}(0,\cdot),\mathbf{i}(0,\cdot),\mathbf{r}(0,\cdot)\in C^1(\mathbb{T})$ with $\int_{\mathbb{T}}(\mathbf{s}+\mathbf{i}+\mathbf{r})(0,x)\,dx=1$; that the lattice initial data are the cell averages $S_\varepsilon(0,x_i)=\varepsilon^{-1}\int_{x_i-\varepsilon/2}^{x_i+\varepsilon/2}\mathbf{s}(0,y)\,dy$, and likewise for $I_\varepsilon(0)$ and $R_\varepsilon(0)$; that $\inf_{x\in\mathbb{T}}\mathbf{s}(0,x)\ge c$ for some constant $c>0$; and that $\alpha\in C^1(\mathbb{T})$ and $\beta\in C^2(\mathbb{T})$. Embed $\Psi_\varepsilon$ as a step-function-valued process $\mathscr{Y}_\varepsilon=(u_\varepsilon,v_\varepsilon,w_\varepsilon)$. For every $\gamma>3/2$ it is tight in $C([0,T];(H^{-\gamma})^3)$, and for $3/2<\gamma<2$ it converges in law, in $C([0,T];(H^{-\gamma})^3)\cap L^2(0,T;(H^{-1})^3)$, to the solution $\mathscr{Y}=(u,v,w)$ of the linear SPDE system obtained by linearizing the reaction-diffusion system around $(\mathbf{s},\mathbf{i},\mathbf{r})$ (with infection-term partial derivatives $\beta\,\mathbf{i}(\mathbf{i}+\mathbf{r})/\mathbf{a}^2$ and $\beta\,\mathbf{s}(\mathbf{s}+\mathbf{r})/\mathbf{a}^2$), driven by the Gaussian martingales

    $$\begin{aligned}
    \langle\mathscr{M}^S(t),\varphi\rangle&=-\!\int_0^t\!\!\int\varphi\sqrt{\tfrac{\beta\mathbf{s}\mathbf{i}}{\mathbf{a}}}\,\dot W_1-\sqrt{2\mu_S}\!\int_0^t\!\!\int\varphi'\sqrt{\mathbf{s}}\,\dot W_2,\\
    \langle\mathscr{M}^I(t),\varphi\rangle&=\int_0^t\!\!\int\varphi\sqrt{\tfrac{\beta\mathbf{s}\mathbf{i}}{\mathbf{a}}}\,\dot W_1+\int_0^t\!\!\int\varphi\sqrt{\alpha\mathbf{i}}\,\dot W_3-\sqrt{2\mu_I}\!\int_0^t\!\!\int\varphi'\sqrt{\mathbf{i}}\,\dot W_4,\\
    \langle\mathscr{M}^R(t),\varphi\rangle&=-\!\int_0^t\!\!\int\varphi\sqrt{\alpha\mathbf{i}}\,\dot W_3-\sqrt{2\mu_R}\!\int_0^t\!\!\int\varphi'\sqrt{\mathbf{r}}\,\dot W_5,
    \end{aligned}$$

    with $\dot W_1,\dots,\dot W_5$ independent space-time white noises.

## Expansion

At fixed $\varepsilon$ the model is a density-dependent Markov jump process in $\mathbb{R}^{3\ell}$, so Kurtz's theorem gives the Gaussian limit $\Psi_\varepsilon$. Passing to $\varepsilon\to0$, the reaction noise (infection $\dot W_1$ shared with opposite signs by $S$ and $I$, recovery $\dot W_3$ shared by $I$ and $R$) has local intensity, while migration between neighbours produces noise of conservative form $\partial_x(\sqrt{2\mu_J J}\,\dot W)$, which tested against $\varphi$ gives the $\varphi'$ terms. Tightness in negative Sobolev spaces uses Kotelenez's maximal inequality for stochastic convolutions with the contraction semigroup of $\mu_J\Delta_\varepsilon$, which is why $\gamma>3/2$ is needed; the limit is identified through the mild formulation of the linearized system.

## Sources

- Thierry Gallouët, Etienne Pardoux and Ténan Yeo, "A SIR epidemic model on a refining spatial grid II-central limit theorem", Stochastics and Partial Differential Equations: Analysis and Computations (2024), <https://doi.org/10.1007/s40072-024-00333-0>; numbering as in arXiv:2412.06480: Section 1 (model and Theorems 1.1-1.3 recalled from N'zi, Pardoux and Yeo), Theorem 2.1, Proposition on convergence of the Gaussian martingales (Section 3), Theorems 3.1 and 3.2.
