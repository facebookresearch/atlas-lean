# Generalized Lotka–Volterra reduction of trait-structured competition

**Model.** $N$ populations carry continuous phenotypic traits $x_i \in \Omega_i$ (smooth bounded domains). Mutation acts as diffusion in trait space with rate $d_i>0$, the intrinsic growth rate $r_i(x_i)$ depends on the trait (with a single interior maximum $r_{i,M}>0$), but interactions depend only on total population sizes:
$$\partial_t u_i = d_i\Delta u_i + u_i\Big(r_i(x_i) - \sum_{j=1}^N a_{ij}\rho_j(t)\Big), \quad \partial_\nu u_i = 0 \text{ on } \partial\Omega_i, \qquad \rho_i(t) = \int_{\Omega_i}u_i(x,t)\,dx.$$
Let $\lambda_i$ be the principal Neumann eigenvalue of $-d_i\Delta - r_i$ with positive eigenfunction $p_i$ normalized by $\int_{\Omega_i}p_i = 1$, i.e. $-d_i\Delta p_i = p_i(r_i + \lambda_i)$, and consider the generalized Lotka–Volterra (GLV) system
$$\dot{\hat\rho}_i = \hat\rho_i\Big(-\lambda_i - \sum_{j=1}^N a_{ij}\hat\rho_j\Big), \qquad i = 1,\dots,N.$$

**Theorem (bounded trait domains).** Suppose the GLV system has a unique equilibrium $\rho^*$ with all $\rho^*_i > 0$, every $\lambda_i < 0$, and either (a) $A = (a_{ij})$ is Lyapunov diagonally stable, or (b) $a_{ij} > 0$ for all $i,j$, or $a_{ij} \le 0$ for all $i \ne j$. Then
$$\rho(t) \to \rho^*, \qquad \Big\|\frac{u_i(\cdot,t)}{\rho_i(t)} - p_i\Big\|_{L^\infty(\Omega_i)} \to 0 \qquad (t\to\infty).$$
If instead (c) $a_{ij} = a_i > 0$ for all $i,j$ and $\lambda_{\underline i}/a_{\underline i}$ is the unique minimum of $\lambda_i/a_i$ and is negative, then all populations except $\underline i$ vanish in $L^\infty$, $\rho_{\underline i}(t) \to -\lambda_{\underline i}/a_{\underline i}$, and $u_{\underline i}/\rho_{\underline i} \to p_{\underline i}$: under such diffuse competition the species with the most negative scaled eigenvalue wins, which in a static environment favors the smallest mutation rate.

**Shifting environments.** On $\mathbb R^n$ with optimal traits moving at constant speeds, $r_i(x_i - \tilde c_i t)$, the same conclusion holds for the totals $\rho$ with a GLV system whose effective rates depend on the shift speeds; an intermediate mutation rate can then be selected.

## Expansion

The substitution $\tilde u_i = u_i\exp\big(\int_0^t\sum_j a_{ij}\rho_j\,ds + \lambda_i t\big)$ decouples the system into $N$ linear parabolic equations, whose solutions align with the principal eigenfunctions $p_i$ at an exponential rate. Integrating over traits then shows that $\rho$ solves the GLV system up to a perturbation decaying in time, i.e. an asymptotically autonomous ODE. Once $\rho$ is shown to be bounded, a general result on asymptotically autonomous systems transfers the global attractor of the GLV system (a global equilibrium under the Lyapunov-stability hypotheses) to $\rho$.

## Sources

- Manh Hong Duong, Nataliya Balabanova and Blaine van Rensburg, "Global Dynamics of Trait-Structured Generalised Lotka-Volterra Systems with Trait-Independent Interactions", arXiv:2607.25573 (2026), Theorem 2.1 and Corollary 2.1 (bounded trait domains), Theorem 2.2 (shifting environments), Theorem 4.1 (asymptotically autonomous systems, quoted), <https://doi.org/10.48550/arXiv.2607.25573>.
