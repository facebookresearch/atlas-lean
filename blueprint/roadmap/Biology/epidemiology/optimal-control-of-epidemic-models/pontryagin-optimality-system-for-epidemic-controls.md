# Pontryagin optimality system for time-dependent epidemic controls

**Control problem.** Let $x(t) \in \mathbb{R}^n_{\ge 0}$ be the state of a compartmental epidemic model
driven by controls $u(t) = (u_1(t), \dots, u_m(t))$ (vaccination, prevention, treatment or awareness
efforts):

$$\dot x = f(x, u), \qquad x(0) = x_0, \qquad t \in [0, T],$$

with admissible controls $\mathcal{U} = \{ u \text{ Lebesgue measurable} : 0 \le u_j(t) \le u_j^{\max} \}$.
The typical objective trades disease burden against a quadratic control cost,

$$J(u) = \int_0^T \Bigl( \sum_{i \in \mathcal{I}} A_i x_i(t) + \frac{1}{2} \sum_{j=1}^{m} B_j u_j(t)^2 \Bigr) dt,
\qquad A_i \ge 0,\ B_j > 0,$$

to be minimized over $\mathcal{U}$, where $\mathcal{I}$ indexes the infected (or otherwise penalized)
classes.

**Existence (Fleming–Rishel conditions).** An optimal $u^* \in \mathcal{U}$ exists if (i) the
admissible set of control–state pairs is nonempty; (ii) the control set
$\prod_j [0, u_j^{\max}]$ is closed and convex; (iii) the right-hand side $f$ is continuous and
bounded by a linear function of the state and control; (iv) the integrand $L(x, u)$ is convex in
$u$; and (v) $L(x, u) \ge c_1 \lVert u \rVert^{\beta} - c_2$ for some $c_1 > 0$ and $\beta > 1$. For
compartmental models with bounded solutions, $f$ affine in $u$ and the quadratic cost above, all five
hold (with $\beta = 2$).

**Necessary conditions (Pontryagin maximum principle).** With the Hamiltonian
$H(x, u, \lambda) = L(x, u) + \sum_{i=1}^{n} \lambda_i f_i(x, u)$, an optimal pair $(x^*, u^*)$ admits
adjoint variables $\lambda(t)$ satisfying

$$\dot\lambda_i = -\frac{\partial H}{\partial x_i}(x^*, u^*, \lambda), \qquad \lambda_i(T) = 0
\quad (i = 1, \dots, n),$$

and $u^*(t)$ minimizes $H(x^*(t), \cdot, \lambda(t))$ over the control set. When $f$ is affine in
each $u_j$, the minimizer is the projection of the stationary point onto the bounds:

$$u_j^*(t) = \min\Bigl\{ u_j^{\max},\ \max\Bigl\{ 0,\ -\frac{1}{B_j} \sum_{i=1}^{n} \lambda_i(t)
\frac{\partial f_i}{\partial u_j}\bigl(x^*(t)\bigr) \Bigr\} \Bigr\}.$$

The state equations with initial data, the adjoint equations with terminal data, and this
characterization form the optimality system.

## Expansion

Because $H$ is strictly convex in $u$ (the cost is quadratic and the dynamics affine in the
controls), $\partial H / \partial u_j = 0$ has a unique root, and projecting it onto
$[0, u_j^{\max}]$ gives the pointwise minimizer. For instance, a prevention control that multiplies
incidence by $(1 - u_j)$ moves $\beta S I / N$ from $S$ to $I$, so
$\partial H/\partial u_j = B_j u_j + (\lambda_S - \lambda_I)\beta S I / N$ and
$u_j^* = \min\{u^{\max}, \max\{0, (\lambda_I - \lambda_S)\beta S I/(B_j N)\}\}$: effort is high
exactly when an extra infection is costlier in shadow price than an extra susceptible. The system is
a two-point boundary value problem and is solved by the forward–backward sweep: integrate the state
forward with the current control, the adjoints backward from $\lambda(T) = 0$, update $u$ by the
characterization, and iterate to convergence. Since the state and adjoint solutions are bounded and
the right-hand sides Lipschitz, the optimal control is unique for a sufficiently short horizon $T$.

## Sources

- W. H. Fleming, R. W. Rishel, Deterministic and Stochastic Optimal Control, Springer (1975),
  Chapter III, Theorem 4.1 (existence) and Theorem 5.1 (maximum principle),
  <https://doi.org/10.1007/978-1-4612-6380-7>.
- J. M. Tchuenche, N. Dube, C. P. Bhunu, R. J. Smith, C. T. Bauch, "The impact of media coverage on
  the transmission dynamics of human influenza", BMC Public Health 11 (Suppl 1) (2011) S5, Theorem 3
  (existence) and the control characterization, <https://doi.org/10.1186/1471-2458-11-s1-s5>
  (PMC3317585).
- S. Y. Tchoumi, M. L. Diagne, H. Rwezaura, J. M. Tchuenche, "Malaria and COVID-19 co-dynamics: A
  mathematical model and optimal control", Applied Mathematical Modelling 99 (2021), objective (29),
  adjoint system (31) and control characterization, <https://doi.org/10.1016/j.apm.2021.06.016>
  (PMC8249695).
- A. Omame, M. Abbas, C. P. Onyenegecha, "Backward bifurcation and optimal control in a co-infection
  model for SARS-CoV-2 and ZIKV", Results in Physics 37 (2022) 105481, Eqs. (16)-(18),
  <https://doi.org/10.1016/j.rinp.2022.105481> (PMC8994284).
