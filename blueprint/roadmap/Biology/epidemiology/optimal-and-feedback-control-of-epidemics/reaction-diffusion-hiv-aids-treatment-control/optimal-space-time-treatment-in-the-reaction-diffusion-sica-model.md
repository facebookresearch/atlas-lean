# Optimal space–time treatment in the reaction–diffusion SICA model

**Model.** On a bounded domain $\Omega \subset \mathbb{R}^2$ with $C^{2+\alpha}$ boundary and $Q = [0,T]\times\Omega$, the densities of susceptible ($S$), HIV-infected without AIDS symptoms ($I$), chronic HIV under treatment ($C$) and AIDS ($A$) individuals satisfy, with homogeneous Neumann boundary conditions,

$$\partial_t S = d_S\Delta S + \Lambda - \beta(I + \eta_C C + \eta_A A)S - \mu S + uI,$$

$$\partial_t I = d_I\Delta I + \beta(I + \eta_C C + \eta_A A)S - \xi_3 I + \gamma A + \omega C - uI,$$

$$\partial_t C = d_C\Delta C + \phi I - \xi_2 C, \qquad \partial_t A = d_A\Delta A + \rho I - \xi_1 A,$$

where $\eta_C, \eta_A$ modify the infectiousness of chronic and AIDS individuals, $\phi, \rho, \gamma, \omega$ are treatment and default rates, $\xi_1, \xi_2, \xi_3$ are the total exit rates of the $A$, $C$, $I$ classes, and the control $u \in U_{ad} = \{u \in L^2(Q) : 0 \le u \le 1 \text{ a.e.}\}$ is a treatment intensity that moves infected individuals back to the susceptible class. With weights $a, b > 0$ the treatment program minimizes

$$J(z, u) = \int_\Omega\int_0^T a\, I(t,x)\, dt\, dx + \frac{b}{2}\|u\|^2_{L^2}, \qquad z = (S, I, C, A).$$

**Theorem.**

1. *(Well-posedness.)* For nonnegative parameters, $u \in U_{ad}$ and nonnegative initial data $z^0$ in the domain of the diffusion operator, the system has a unique global strong nonnegative solution $z \in W^{1,2}([0,T]; L^2(\Omega)^4)$ with each component in $L^2(0,T; H^2(\Omega)) \cap L^\infty(0,T; H^1(\Omega)) \cap L^\infty(Q)$, bounded by a constant independent of $u$.
2. *(Existence of an optimal treatment.)* The control problem admits an optimal pair $(z^*, u^*)$.
3. *(Sensitivities.)* The control-to-state map $u \mapsto z(u)$ is Gâteaux differentiable at $u^*$; the derivative $Z$ in direction $u$ solves the linearized system $\partial_t Z = \mathcal{M}Z + F(z^*)Z + u\,R(z^*)$, $Z(0) = 0$, where $\mathcal{M}$ is the diagonal diffusion operator and $F(z^*)$ the Jacobian of the reaction terms.
4. *(Optimality condition.)* The adjoint system has a unique solution $p = (p_1, \dots, p_4)$, and the optimal treatment is

$$u^* = \min\Big(u_{\max},\ \max\Big(0,\ \frac{I^*(p_2 - p_1)}{b}\Big)\Big).$$

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

Written as $z' = \mathcal{M}z + f(z, u)$, the diffusion part generates an analytic contraction semigroup on $L^2(\Omega)^4$ and the reaction part is locally Lipschitz; local strong solutions exist, and $L^\infty$ bounds independent of $u$ (from the total population, which obeys a linear inequality) extend them globally. Nonnegativity follows from the quasi-positivity of the reaction terms. For existence of an optimum, a minimizing sequence of controls is weakly compact in $L^2(Q)$, the uniform bounds give strong $L^2$ convergence of the states by Aubin–Lions, which passes to the limit in the bilinear terms $\beta I S$ and $u I$, and $J$ is weakly lower semicontinuous. Differentiating $J$ along $u^* + \epsilon v$ and using the adjoint to eliminate the state derivative gives $\int_Q (b u^* + I^*(p_1 - p_2))(v - u^*) \ge 0$ for all admissible $v$, whose pointwise projection onto $[0, u_{\max}]$ is the stated formula.

## Sources

- Houssine Zine, Abderrahim El Adraoui, Delfim F. M. Torres, "Mathematical analysis, forecasting and optimal control of HIV/AIDS spatiotemporal transmission with a reaction diffusion SICA model", AIMS Mathematics 7 (2022), 16519–16535, <https://doi.org/10.3934/math.2022904>. Published version of arXiv:2207.02527, cited next; locators there refer to the arXiv version.
- Houssine Zine, Abderrahim El Adraoui, Delfim F. M. Torres, "Mathematical Analysis, Forecasting and Optimal Control of HIV/AIDS Spatiotemporal Transmission with a Reaction Diffusion SICA Model", arXiv (2022). Section 3 (model), Theorems 1, 2, 3, 5, Lemma 4. <https://doi.org/10.48550/arXiv.2207.02527>
