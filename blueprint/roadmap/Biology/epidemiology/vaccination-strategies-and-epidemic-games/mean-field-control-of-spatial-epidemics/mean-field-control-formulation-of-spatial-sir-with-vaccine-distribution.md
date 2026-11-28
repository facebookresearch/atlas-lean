# Mean-field control formulation of spatial SIR with vaccine distribution

**Setting.** On a bounded domain $\Omega \subset \mathbb R^d$ with Neumann boundary conditions, susceptible, infected, recovered and vaccine densities $\rho_S,\rho_I,\rho_R,\rho_V : [0,T]\times\Omega \to [0,\infty)$ move with momenta $m_i = \rho_iv_i$, which are the controls. Infection acts through a symmetric positive-definite kernel, $(K*\rho)(x) = \int_\Omega K(x,y)\rho(y)\,dy$ (Gaussian in the paper). The **SIRV dynamics** are

$$\partial_t\rho_S + \nabla\cdot m_S = -\beta\rho_S\,K*\rho_I + \tfrac{\eta_S^2}{2}\Delta\rho_S - \theta_1\rho_V\rho_S, \qquad \partial_t\rho_I + \nabla\cdot m_I = \beta\rho_S\,K*\rho_I - \gamma\rho_I + \tfrac{\eta_I^2}{2}\Delta\rho_I,$$

$$\partial_t\rho_R + \nabla\cdot m_R = \gamma\rho_I + \tfrac{\eta_R^2}{2}\Delta\rho_R + \theta_1\rho_V\rho_S,$$

with vaccines produced at rate $f(t,x)$ and used at rate $\theta_2\rho_V\rho_S$ during $(0,T')$, $\partial_t\rho_V = f - \theta_2\rho_V\rho_S$, and then delivered, $\partial_t\rho_V + \nabla\cdot m_V = -\theta_2\rho_V\rho_S$ on $[T',T)$. Here $\theta_1$ is vaccine efficiency and $\theta_2$ the utilization rate; total population $\int_\Omega(\rho_S+\rho_I+\rho_R)$ is conserved.

**Variational problem.** Minimize, subject to these constraints,

$$\int_0^T\!\!\int_\Omega \sum_{i\in\{S,I,R\}} F_i(\rho_i,m_i) + \int_{T'}^T\!\!\int_\Omega F_V(\rho_V,m_V) + \int_0^T\big(\mathcal G_P(\rho_S+\rho_I+\rho_R) + \mathcal G_V(\rho_V)\big)dt + \int_0^{T'}\!\mathcal G_0(f)\,dt + \sum_{i\in\{S,I,V\}}\mathcal E_i(\rho_i(T)) + \mathcal E_R(1 - \rho_R(T)),$$

where $F_i(\rho,m) = \alpha_i|m|^2/(2\rho)$ for $\rho > 0$, $F_i(0,0) = 0$ and $F_i(0,m) = \infty$ for $m \ne 0$ is the kinetic (Benamou–Brenier) cost $\frac{\alpha_i}{2}\rho|v|^2$, $\mathcal G_P, \mathcal G_V, \mathcal G_0$ are integral penalties of convex lower-semicontinuous functions on crowding, vaccine concentration and vaccine production, and the terminal costs $\mathcal E$ penalize remaining susceptible, infected and unused vaccine mass and missing recovered mass (quadratic in the paper).

**Properties.** Each $F_i$ is convex, lower semicontinuous and positively 1-homogeneous in $(\rho,m)$, so all costs are convex; the constraints are linear except for the bilinear infection and vaccination terms. Writing the constraints as $A\big((\rho_i,m_i)_i, f\big) = 0$ for a nonlinear operator $A$ and introducing dual variables $p$ gives the saddle-point problem $\min_u\max_p\, g(u) + \langle A(u), p\rangle - f^*(p)$, which is solved by a nonlinear primal-dual hybrid gradient method that linearizes $A$ at the current iterate (in its G-prox form, the source's (3.6)). The convergence result is local: let $(u^*,p^*)$ be a saddle point, i.e. a solution of the optimality system $0\in H_{u^*}(u^*,p^*)$ (the source's (2.17)), with $\lVert\nabla A(u^*)\rVert>0$ and $u\mapsto A(u)$ continuous (3.9), let the cost $g$ be strongly convex (as it is with the quadratic terminal costs, (2.8)), and let the step sizes satisfy $\tau^{(k)}\sigma^{(k)}<1$ for all $k$. Then there exists $\delta>0$ such that for every initial point $(u^{(0)},p^{(0)})$ with $\lVert u^{(0)}-u^*\rVert_{L^2}^2+\lVert p^{(0)}-p^*\rVert_{L^2}^2<\delta^2$ the iterates converge to $(u^*,p^*)$ (Theorem 3.3).

## Expansion

The model extends Kermack–McKendrick SIR in two directions: spatial movement of each compartment is a controlled transport with an optimal-transport cost, and vaccination is an explicit resource with its own production and delivery dynamics, so that the planner trades off moving people and vaccines against infections and crowding. The nonlocal kernel lets infection act at a distance comparable to the kernel width, and the viscosity terms model unplanned diffusion. Because the problem is a constrained convex optimization in the flux variables apart from the bilinear coupling, standard first-order primal-dual splitting applies.

## Sources

- Wonjun Lee, Siting Liu, Wuchen Li and Stanley Osher, "Mean field control problems for vaccine distribution", arXiv:2104.11887 (2021), Section 2 (spatial SIRV continuity equations, vaccine PDE, nonlinear operator $A$ and cost functional), Section 3 (saddle-point formulation, nonlinear primal-dual hybrid gradient algorithm, assumption (3.9) and Theorem 3.3), <https://doi.org/10.48550/arXiv.2104.11887>. Published version: Research in the Mathematical Sciences 9 (2022) 51, <https://doi.org/10.1007/s40687-022-00350-2>.
