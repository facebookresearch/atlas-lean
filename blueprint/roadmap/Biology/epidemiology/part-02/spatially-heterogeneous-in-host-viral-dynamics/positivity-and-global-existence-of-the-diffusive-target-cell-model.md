# Positivity and global existence for the diffusive target-cell model

**Model.** Let $\Omega \subset \mathbb{R}^n$ be a bounded domain with smooth boundary. Uninfected target cells $T(t,x)$, infected cells $I(t,x)$ and free virions $V(t,x)$ diffuse and interact as in the standard in-host viral dynamics model, with a spatially varying supply of target cells:

$$\partial_t T - D_T \Delta T = \lambda(x) - \mu_T T - kTV,$$

$$\partial_t I - D_I \Delta I = kTV - \mu_I I,$$

$$\partial_t V - D_V \Delta V = N\mu_I I - \mu_V V,$$

for $x \in \Omega$, $t \ge 0$, with homogeneous Dirichlet or homogeneous Neumann boundary conditions for all three components. Here $k, N, \mu_T, \mu_I, \mu_V, D_T, D_I, D_V > 0$, $N$ is the burst size, and $\lambda \in C^\infty(\Omega)$ with $\lambda \ge 0$, $\lambda \not\equiv 0$. Initial data $T_0, I_0, V_0$ are continuous, positive and bounded on $\overline{\Omega}$.

**Theorem (local existence).** There is $t^* \in (0, \infty]$ such that the problem has a unique positive classical solution with each component in $C^1((0,t^*); C^2(\Omega))$. This corrects Theorem 2.1 of arXiv:1508.07617, which prints $t^* \in [0,\infty]$; the value $t^*=0$ would assert nothing, and the source's contraction argument gives a positive existence time.

**Theorem (positivity, bounds, global existence).** For every $t^* > 0$ the solution exists on $(0, t^*) \times \Omega$, satisfies $T, I, V > 0$, and there are constants $C, C_{t^*} > 0$ with

$$\|T(t)\|_\infty \le C, \qquad \|I(t)\|_\infty + \|V(t)\|_\infty \le C_{t^*} \quad \text{for all } t \in [0, t^*].$$

**Theorem (regularity).** If the initial data lie in $L^2(\Omega)$, then for every $t \in (0, t^*)$ the components belong to $H^m(\Omega)$ for all $m \in \mathbb{N}$.

These results hold in every dimension $n$ and do not depend on the diffusion coefficients.

## Expansion

Local existence follows from the contraction mapping principle applied to the mild (heat-semigroup) formulation. Positivity uses the parabolic maximum principle component by component. The bound on $T$ follows by comparing $T$ with the solution of the linear problem $\partial_t u - D_T\Delta u = \lambda(x) - \mu_T u$, since $-kTV \le 0$. The infection term appears with a minus sign in the $T$ equation and a plus sign in the $I$ equation: this exact transfer of mass prevents blow-up. If the sign in the $T$ equation were reversed, the system would behave like $u_t - \Delta u = uv$, $v_t - \Delta v = uv$, whose solutions can blow up in finite time. Regularity follows from energy estimates for the gradients, bootstrapped to every Sobolev order.

## Sources

- S. Pankavich and C. Parkinson, "Mathematical analysis of an in-host model of viral dynamics with spatial heterogeneity", arXiv:1508.07617 (2015): model (3CM) in Section 2.1; Theorems 2.1 (local existence), 2.2 (positivity, bounds and global existence) and 2.3 (regularity) in Section 2.2. <https://doi.org/10.48550/arXiv.1508.07617>. Published version: Discrete and Continuous Dynamical Systems - B 21(4) (2016), 1237–1257, <https://doi.org/10.3934/dcdsb.2016.21.1237>; locators above refer to the arXiv version.
