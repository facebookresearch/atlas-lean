# Well-posedness of the reaction–diffusion sterile insect model

**Model.** For Sterile Insect Technique (SIT) control of *Aedes aegypti*, let $M(x,t)$, $F(x,t)$, $M_S(x,t)$ be the densities of wild males, wild females and released sterile males on a bounded smooth habitat $\Omega\subset\mathbb{R}^2$. Females mate with a wild male with probability $M/(M+\gamma M_S)$, where $0<\gamma\le1$ is the relative mating competitiveness of sterile males; larval competition enters through the Ricker factor $e^{-\sigma(M+F)}$. With diffusivities $\alpha_M,\alpha_F,\alpha_S>0$,

$$\partial_tM=\alpha_M\Delta M+r\rho\,\frac{FM}{M+\gamma M_S}\,e^{-\sigma(M+F)}-\mu_MM,$$

$$\partial_tF=\alpha_F\Delta F+(1-r)\rho\,\frac{FM}{M+\gamma M_S}\,e^{-\sigma(M+F)}-\mu_FF,$$

$$\partial_tM_S=\alpha_S\Delta M_S+\Lambda-\mu_SM_S,$$

with homogeneous Neumann boundary conditions, sex ratio $r\in[0,1]$, fecundity $\rho>0$, mortalities $\mu_M,\mu_F,\mu_S>0$ and daily release rate $\Lambda\ge0$, taken constant in time for the analysis (simulations also use heterogeneous and impulsive releases). Initial data satisfy $M_0>0$, $F_0\ge0$, $M_{S0}\ge0$ with $M_{S0}\not\equiv0$. Without diffusion this is the Ricker-type SIT model of Bliman and coauthors.

**Proposition (local Lipschitz bound).** Write $G(X)=\frac{FM}{M+\gamma M_S}e^{-\sigma(M+F)}$ for $X=(M,F,M_S)\ge0$. For $M+\gamma M_S>0$,

$$|G(X)-G(\hat X)|\le\frac{L(X)}{M+\gamma M_S}\,|X-\hat X|,\qquad L(X)=\sigma FM+F+\gamma^2(F+M_S)+1 ,$$

and the full reaction term is Lipschitz with constant $\max\{r,1-r\}\rho L(X)/(M+\gamma M_S)+\max\{\mu_M,\mu_F,\mu_S\}$.

**Proposition (sterile males stay positive).** If $M_{S0}\ge0$ and $M_{S0}\not\equiv0$, then for every $T>\epsilon>0$ there is $\delta>0$ with $M_S(\cdot,t)\ge\delta$ on $\Omega$ for all $t\in[\epsilon,T]$. Hence the mating denominator $M+\gamma M_S$ stays away from zero after any positive time.

**Theorem.** For all initial data as above, the system has a unique global solution, and it is nonnegative and bounded:

$$M,F,M_S\ge0,\qquad \sup_{t\ge0}\big\|(M,F,M_S)(\cdot,t)\big\|_{L^\infty(\Omega)}<\infty .$$

## Expansion

The sterile-male equation is linear and decoupled, and the strong maximum principle for the Neumann heat semigroup gives its uniform positivity on $[\epsilon,T]$; positivity of $M_0$ covers the initial layer. With the denominator bounded below, the reaction term is locally Lipschitz, which gives local existence and uniqueness. Nonnegativity follows from the invariance principle for parabolic systems: on each face $\{X_i=0\}$ the $i$-th reaction component is nonnegative. Because $G\le F$ and the Ricker factor is at most one, the reaction obeys a linear growth bound $|f(X)|\le C_1|X|+C_2$, and a standard a priori $L^\infty$ estimate for such reaction–diffusion systems gives the uniform bound, hence global existence. Simulations show a critical release-size threshold separating eradication from persistence at a reduced equilibrium, matching the ODE dynamics.

## Sources

- Oscar Eduardo Escobar-Lasso, Stefan Frei, Reinhard Racke, Olga Vasilieva, "Analysis and numerical simulation of a spatio-temporal Ricker-type model for the control of Aedes aegypti mosquitoes with Sterile Insect Techniques", arXiv:2603.24460 (2026): model in Section 2, Proposition 1 (Lipschitz bound), Proposition 2 (lower bound on $M_S$), Theorem 1 (global well-posedness), Section 3; release threshold simulations in Section 5. <https://doi.org/10.48550/arXiv.2603.24460>
