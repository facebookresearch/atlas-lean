# Steady-state sensitivities and retraction to the steady-state manifold

Let $\dot x = f(x, \theta, u)$ with $f$ continuously differentiable, state $x \in \mathbb R^{n_x}$, parameters $\theta \in \mathbb R^{n_\theta}$ and input $u$. Fitting perturbation data from experiments $e = 1, \dots, E$, each starting at a steady state of a control input $u^e_c$, is the problem

$$\min_{\theta,\, x_s^1, \dots, x_s^E} J(\theta, x_s^1, \dots, x_s^E) \quad \text{s.t.} \quad f(x_s^e, \theta, u_c^e) = 0, \quad e = 1, \dots, E .$$

1. **Steady-state sensitivity.** If $x_s$ is a locally exponentially stable steady state for $(\theta, u)$, then $\partial f/\partial x$ is invertible there, the steady state is locally a smooth function $x_s(\theta, u)$, and its sensitivity is

    $$S(\theta, x_s, u) = \frac{\partial x_s}{\partial \theta} = -\left(\frac{\partial f}{\partial x}\right)^{-1} \frac{\partial f}{\partial \theta}. \tag{12}$$

    Hence $x_s(\theta + r\Delta\theta, u) = x_s(\theta, u) + S\, r\Delta\theta + O(r^2)$, and the ODE $dx_s/dr = S(\theta + r\Delta\theta, x_s, u)\,\Delta\theta$ moves along the steady-state manifold.
2. **Reduced gradient.** Eliminating the constraint by solving for the steady states gives the objective $\theta \mapsto J(\theta, x_s^1(\theta), \dots)$, with gradient

    $$\frac{dJ}{d\theta} = \frac{\partial J}{\partial \theta} + \sum_{e=1}^{E} \frac{\partial J}{\partial x_s^e}\, S(\theta, x_s^e, u_c^e). \tag{15}$$

3. **Continuous analogue with retraction.** For a descent direction $g$ (for example $g = (dJ/d\theta)^{\mathsf T}$, or the Fisher-information Newton direction $(F + \mu I)^{-1}(dJ/d\theta)^{\mathsf T}$) and a retraction factor $\lambda > 0$, consider

    $$\frac{d\theta}{dr} = -g(\theta, x_s^1, \dots, x_s^E), \qquad \frac{dx_s^e}{dr} = \hat S(\theta, x_s^e, u_c^e)\,\frac{d\theta}{dr} + \lambda f(x_s^e, \theta, u_c^e), \tag{17}$$

    with $\hat S = -(\partial f/\partial x)^{+}\, \partial f/\partial \theta$ (Moore–Penrose pseudoinverse), which equals $S$ on the manifold. Along trajectories on the manifold $J$ decreases. For the gradient direction and suitable $\lambda$, local optima of the constrained problem are locally exponentially stable equilibria of (17), so the problem can be solved with adaptive stiff ODE solvers. Initial points need not satisfy the steady-state constraint.

## Proof depends on

- [Implicit function theorem](../../../../Analysis/real-functions/multivariable-calculus/implicit-function-theorem.md)

## Expansion

The forward sensitivity equation $\dot S = (\partial f/\partial x) S + \partial f/\partial \theta$ reduces at a steady state ($\dot S = 0$) to (12). Equivalently, apply the implicit function theorem to $f(x_s(\theta), \theta, u) = 0$, which is possible because local exponential stability makes $\partial f/\partial x$ Hurwitz and hence invertible. Equation (15) is the chain rule. In (17), the term $\lambda f$ pulls the state back toward the manifold at rate about $\lambda$ times the stability margin, because $\partial f/\partial x$ is stable near it. For $\lambda \gg 1$ trajectories first collapse onto the manifold and then descend along it. For the conversion $A \rightleftharpoons B$ with $\dot x = \theta_2 - (\theta_1 u + \theta_2)x$, the steady state is $x_s = \theta_2/(\theta_1 u + \theta_2)$ and (12) gives $S = \bigl(-x_s u,\ 1 - x_s\bigr)/(\theta_1 u + \theta_2)$ without solving for $x_s$. A hybrid alternative retracts numerically after each optimizer step and uses (15) for gradients. Both converged more often, and with less computation per converged start, than generic constrained optimizers on ERK-signaling models.

## Sources

- A. Fiedler, S. Raeth, F. J. Theis, A. Hausser, J. Hasenauer, "Tailored parameter optimization methods for ordinary differential equation models with steady-state constraints", *BMC Systems Biology* (2016), Methods (Eqs. (6)–(18): manifold of steady states, hybrid and simulation-based optimization) and Results (conversion process, Eqs. (19)–(25)), <https://doi.org/10.1186/s12918-016-0319-7> (PMC4994295).
