# Spreading–vanishing dichotomy for a seasonal, impulsively controlled nonlocal dengue model

**Model.** Let $u_1(x,t)$ and $u_2(x,t)$ be the densities of infected humans and infected mosquitoes on a moving infected interval $(p(t),q(t))$, with $q(0)=-p(0)=q_0>0$. Dispersal is nonlocal, $\mathcal L_i[u_i]=\int_{p(t)}^{q(t)}J_i(x-y)u_i(y,t)\,dy-u_i(x,t)$, with kernels $J_i\in C(\mathbb R)\cap L^\infty(\mathbb R)$ symmetric, $\int J_i=1$, $J_i(0)>0$. Each period $[kT,(k+1)T]$ consists of a dry season of length $\tau<T$ followed by a wet season. At $t=kT$ a vector-control impulse replaces $u_2$ by $G(u_2)$, where $G\in C^1[0,\infty)$, $G(0)=0$, $G'>0$, and $G(u)/u\in(0,1]$ is non-increasing.

- Dry season $t\in(kT,kT+\tau]$: $u_{1t}=d_1\mathcal L_1[u_1]-\delta_1u_1$, $u_{2t}=-\delta_2u_2$, and the boundaries are frozen.
- Wet season $t\in(kT+\tau,(k+1)T]$:

$$u_{1t}=d_1\mathcal L_1[u_1]+\alpha_1(\beta_1-u_1)u_2-(\gamma_1+\nu_1)u_1,\qquad u_{2t}=d_2\mathcal L_2[u_2]+\alpha_2(\beta_2-u_2)u_1-\gamma_2u_2,$$

$$q'(t)=\sum_{i=1}^2\mu_i\int_{p(t)}^{q(t)}\!\int_{q(t)}^{\infty}J_i(x-y)\,u_i(x,t)\,dy\,dx,\qquad p'(t)=-\sum_{i=1}^2\mu_i\int_{p(t)}^{q(t)}\!\int_{-\infty}^{p(t)}J_i(x-y)\,u_i(x,t)\,dy\,dx,$$

with $u_i=0$ at $x=p(t),q(t)$ and initial data $u_{i,0}\in C([-q_0,q_0])$, $u_{i,0}(\pm q_0)=0$, $0<u_{i,0}\le\beta_i$. Here $\beta_1,\beta_2$ are the total human and mosquito carrying levels, $\alpha_i$ the transmission rates and $\mu_i>0$ the expansion capacities.

For an interval $[r_1,r_2]$ let $\lambda_1([r_1,r_2])$ be the principal eigenvalue of the $T$-periodic linearized problem at $0$ on $[r_1,r_2]$ (the linearization of the two seasonal systems, with the jump $\psi_2(\cdot,0^+)=G'(0)\psi_2(\cdot,0)$), and $\lambda_1([-\infty,\infty])$ its limit on the whole line.

**Theorem.** The problem has a unique positive solution with $0<u_i\le\beta_i$, and $p_\infty=\lim p(t)$, $q_\infty=\lim q(t)$ exist in $[-\infty,\infty]$. Exactly one of the following occurs.

1. **Vanishing:** $q_\infty-p_\infty<\infty$ and $u_i(\cdot,t)\to0$ uniformly on $[p(t),q(t)]$.
2. **Spreading:** $q_\infty-p_\infty=\infty$ and $u_i(x,t+sT)\to\overline U_i(t)$ as $s\to\infty$, locally uniformly in $x\in\mathbb R$ and uniformly in $t\in[0,T]$, where $(\overline U_1,\overline U_2)$ is the unique positive $T$-periodic solution of the spatially homogeneous impulsive seasonal system.

If $J_1=J_2$, the linearized problem has a unique principal eigenvalue and:

- if $\lambda_1([-\infty,\infty])\ge0$, vanishing always happens; in particular vanishing always happens when $\tau=T$ (no wet season);
- if $\lambda_1([-\infty,\infty])<0$ and $\lambda_1([-q_0,q_0])\le0$, spreading always happens;
- if $\lambda_1([-\infty,\infty])<0<\lambda_1([-q_0,q_0])$, then for given initial data there are $\tilde\mu\ge\hat\mu>0$ such that spreading occurs when $\mu_1+\mu_2>\tilde\mu$ and vanishing when $\mu_1+\mu_2<\hat\mu$; with $\mu_2=\rho\mu_1$ fixed there is a sharp threshold $\mu^\ast>0$ (spreading for $\mu_1>\mu^\ast$, vanishing for $\mu_1<\mu^\ast$); and for fixed $\mu_i$ vanishing occurs when the initial data are small enough.

Moreover, for $J_1=J_2$, $0\le\tau<T$, $\delta_1\ge\gamma_1+\nu_1$ and $\delta_2\ge\gamma_2-d_2\lambda_0$, the principal eigenvalue $\lambda_1$ is continuous and strictly increasing in the dry-season length $\tau$: longer dry seasons favor extinction.

## Expansion

Well-posedness follows from a contraction argument on each season with the boundaries as unknowns, using that the wet-season boundary velocities are positive and bounded. The comparison principle for the impulsive free-boundary system lets one sandwich the solution between solutions of fixed-boundary problems. On a fixed interval the sign of $\lambda_1$ decides between extinction ($\lambda_1\ge0$) and convergence to a positive periodic state ($\lambda_1<0$), proved with upper and lower solutions built from the principal eigenfunction. If the limiting interval is bounded, the solution must die out there, which forces $\lambda_1([p_\infty,q_\infty])\ge0$; if it is unbounded, monotonicity of $\lambda_1$ in the interval gives convergence to the homogeneous periodic state. When $J_1=J_2$, separation of variables $\psi_i(x,t)=\psi(x)f_i(t)$ reduces the eigenvalue problem to a periodic ODE problem, which gives existence and uniqueness of $\lambda_1$ and its monotonicity in $\tau$. The thresholds in $\mu_1+\mu_2$ come from the monotone dependence of $q_\infty-p_\infty$ on the expansion capacities.

## Sources

- Han Zhang, Zhigui Lin, Huaiping Zhu, "On a nonlocal dengue model with moving boundaries: The impact of dry-wet season and impulsive intervention", arXiv (2026). Section 1 (model (1.2)–(1.3), assumptions (A1), (A2), (J)), Theorem 2.1, Theorem 2.2, Lemma 2.6, Theorem 4.7, Corollary 4.1, Theorem 4.12, Theorem 4.13. <https://doi.org/10.48550/arXiv.2609.21235>
