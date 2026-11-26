# Pontryagin optimality system for epidemic controls with quadratic costs

**Setting.** A compartmental epidemic model with state $x(t) \in \mathbb{R}^n_{\ge 0}$ (susceptible, infected, environmental, ... classes) is controlled by $m$ time-dependent intensities $u = (u_1, \dots, u_m)$, each entering the vector field affinely (for example a factor $(1 - u_k)$ on a transmission rate, or an added removal rate $u_k$):
$$\dot x = f(x) + \sum_{k=1}^m u_k\, g_k(x), \qquad x(0) = x_0, \qquad t \in [0, t_f].$$
Admissible controls are Lebesgue measurable with $u_k(t) \in [0, u_k^{\max}]$, $u_k^{\max} \le 1$ where $(1-u_k)$ must stay nonnegative. The cost to be minimized is
$$J(u) = \int_0^{t_f} \Big( c^\top x(t) + \sum_{k=1}^m \frac{b_k}{2}\, u_k(t)^2 \Big)\, dt, \qquad c \ge 0,\ b_k > 0,$$
where $c^\top x$ weights the burden of infected classes and $b_k u_k^2/2$ the (increasing marginal) cost of applying control $k$.

**Theorem.**
1. *(Existence, Filippov–Cesari.)* If the solutions are bounded uniformly over admissible controls (the right-hand side is bounded by a linear function of state and control), the control set is closed, convex and bounded, and the integrand is convex in $u$ and bounded below by $\underline{b}\,|u|^2$ with $\underline{b} = \min_k b_k / 2 > 0$, then an optimal control $u^\ast$ exists.
2. *(Necessary conditions, Pontryagin.)* With the Hamiltonian
$$H(x, u, \lambda) = c^\top x + \sum_k \frac{b_k}{2} u_k^2 + \lambda^\top\Big(f(x) + \sum_k u_k g_k(x)\Big),$$
there is an adjoint $\lambda(t) \in \mathbb{R}^n$ with
$$\dot \lambda = -\frac{\partial H}{\partial x}(x^\ast, u^\ast, \lambda), \qquad \lambda(t_f) = 0,$$
and $u^\ast(t)$ minimizes $H$ pointwise over the control box. Because $H$ is strictly convex and separable in the $u_k$, this gives the characterization
$$u_k^\ast(t) = \min\Big\{ u_k^{\max},\ \max\Big\{ 0,\ -\frac{\lambda(t)^\top g_k(x^\ast(t))}{b_k} \Big\} \Big\}.$$
3. The state equation with $u = u^\ast$, the adjoint equation and this projection formula form the **optimality system**, a two-point boundary value problem (initial condition on $x$, terminal condition on $\lambda$), usually solved by the forward–backward sweep method.

## Depends on

- [Basic reproduction number of the next-generation matrix](../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Existence uses compactness of the admissible set in the weak topology together with convexity of the integrand in the control and the a priori bounds on solutions. For the characterization, $\partial H / \partial u_k = b_k u_k + \lambda^\top g_k(x)$, so the unconstrained minimizer is $u_k = -\lambda^\top g_k / b_k$; minimizing a strictly convex quadratic in one variable over an interval gives the projection of that value onto $[0, u_k^{\max}]$. For a control reducing transmission $\beta S I$ by a factor $(1 - u_k)$ between the susceptible and exposed classes, $\lambda^\top g_k = \beta S I\,(\lambda_S - \lambda_E)$ and the formula reads $u_k^\ast = \min\{u_k^{\max}, \max\{0, \beta S I(\lambda_E - \lambda_S)/b_k\}\}$: control is applied when an infection is worth more in the adjoint (shadow price) of the exposed class than of the susceptible class. Quadratic costs make $u^\ast$ continuous in the state and adjoint; linear costs instead give bang–bang and singular arcs.

## Sources

- J. K. K. Asamoah, M. A. Owusu, Z. Jin, F. T. Oduro, A. Abidemi and E. O. Gyasi, "Global stability and cost-effectiveness analysis of COVID-19 considering the impact of the environment: using data from Ghana", Chaos, Solitons & Fractals 140 (2020), 110103, Section 4 (objective functional (19), constrained system (20), existence conditions and Hamiltonian), <https://doi.org/10.1016/j.chaos.2020.110103>, PMCID: PMC7351453.
- W. H. Fleming and R. W. Rishel, *Deterministic and Stochastic Optimal Control*, Springer (1975), Chapter III.
- S. Lenhart and J. T. Workman, *Optimal Control Applied to Biological Models*, Chapman & Hall/CRC (2007), Chapters 1–4.
