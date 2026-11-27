# Pontryagin optimality system for epidemic controls with quadratic costs

**Setting.** A compartmental epidemic model with state $x(t) \in \mathbb{R}^n_{\ge 0}$ (susceptible, infected, environmental, ... classes) is controlled on a finite horizon $[0, t_f]$ by $m$ time-dependent intensities $u = (u_1, \dots, u_m)$, each entering the vector field affinely (for example a factor $(1 - u_k)$ on a transmission rate, an added removal rate $u_k$, or a vaccination flux $u_k S$):

$$\dot x = f(x) + \sum_{k=1}^m u_k\, g_k(x), \qquad x(0) = x_0, \qquad t \in [0, t_f],$$

with $f$ and the $g_k$ continuously differentiable. Admissible controls are Lebesgue measurable with $u_k(t) \in [0, u_k^{\max}]$ ($u_k^{\max} \le 1$ where $(1-u_k)$ must stay nonnegative), and the terminal state is free. The cost to be minimized is

$$J(u) = \int_0^{t_f} \Big( c^\top x(t) + \sum_{k=1}^m \frac{b_k}{2}\, u_k(t)^2 \Big)\, dt, \qquad c \ge 0,\ b_k > 0,$$

where $c^\top x$ weights the burden of infected classes and $b_k u_k^2/2$ the increasing marginal cost of applying control $k$. (Sources that write the cost as $B_k u_k^2$ correspond to $b_k = 2B_k$.)

**Theorem.**

1. *(Existence.)* If the solutions are bounded on $[0, t_f]$ uniformly over admissible controls and the right-hand side is bounded by a linear function of state and control, then an optimal control $u^\ast$ exists: the control set is closed, convex and bounded, and the integrand is convex in $u$ and bounded below by $\underline{b}\,|u|^2$ with $\underline{b} = \min_k b_k / 2 > 0$ (Fleming–Rishel conditions).
2. *(Necessary conditions.)* With the Hamiltonian

$$H(x, u, \lambda) = c^\top x + \sum_k \frac{b_k}{2} u_k^2 + \lambda^\top\Big(f(x) + \sum_k u_k g_k(x)\Big),$$

an optimal pair $(x^\ast, u^\ast)$ admits an absolutely continuous adjoint $\lambda(t) \in \mathbb{R}^n$ with

$$\dot \lambda = -\frac{\partial H}{\partial x}(x^\ast, u^\ast, \lambda), \qquad \lambda(t_f) = 0,$$

and $u^\ast(t)$ minimizes $H(x^\ast(t), \cdot, \lambda(t))$ over the control box for almost every $t$. Because $H$ is strictly convex and separable in the $u_k$, this gives the componentwise projection

$$u_k^\ast(t) = \min\Big\{ u_k^{\max},\ \max\Big\{ 0,\ -\frac{\lambda(t)^\top g_k(x^\ast(t))}{b_k} \Big\} \Big\}.$$

3. The state equation with $u = u^\ast$, the adjoint equation and this projection formula form the **optimality system**, a two-point boundary value problem (initial condition on $x$, terminal condition on $\lambda$).

For a control moving individuals from compartment $p$ to compartment $q$ at per-capita rate $u_k$ (vaccinating susceptibles $S \to V$, quarantining exposed $E \to Q$, treating $H \to R$), $\lambda^\top g_k = (\lambda_q - \lambda_p) x_p$ and

$$u_k^\ast = \min\Big\{ u_k^{\max},\ \max\Big\{0,\ \frac{(\lambda_p - \lambda_q)\, x_p}{b_k}\Big\}\Big\}.$$

## Expansion

Existence uses compactness of the admissible set in the weak topology together with convexity of the integrand in the control and the a priori bounds on solutions. For the characterization, $\partial H / \partial u_k = b_k u_k + \lambda^\top g_k(x)$, so the unconstrained minimizer is $u_k = -\lambda^\top g_k / b_k$; minimizing a strictly convex quadratic in one variable over an interval gives the projection of that value onto $[0, u_k^{\max}]$. The adjoint $\lambda_i(t)$ is the shadow cost of one more individual in compartment $i$ at time $t$, so effort is high when moving people between compartments reduces future cost and the source compartment is large, and it switches off near $t_f$ as the adjoints vanish. For a control reducing transmission $\beta S I$ by a factor $(1 - u_k)$ between the susceptible and exposed classes, $\lambda^\top g_k = \beta S I\,(\lambda_S - \lambda_E)$ and the formula reads $u_k^\ast = \min\{u_k^{\max}, \max\{0, \beta S I(\lambda_E - \lambda_S)/b_k\}\}$. Quadratic costs make $u^\ast$ continuous in the state and adjoint; linear costs instead give bang–bang and singular arcs. Since state and adjoint solutions are bounded and the right-hand sides Lipschitz, a contraction argument gives uniqueness of the solution of the optimality system for a sufficiently short horizon. Numerically the system is solved by the forward–backward sweep: integrate the state forward with the current control, the adjoints backward from $\lambda(t_f) = 0$, update the control by the projection formula, and iterate to convergence.

Applications include COVID-19 models with vaccination and treatment, with contact tracing and isolation of asymptomatic and quarantined classes, with preventive measures in Benin and with an environmental compartment in Ghana; COVID-19–dengue, COVID-19–influenza, malaria–COVID-19 and SARS-CoV-2–Zika co-infection models; and an influenza model with media-reduced contact rates. Strategy costs computed this way feed the [cost-effectiveness ratios of control strategies](incremental-cost-effectiveness-ratio-of-control-strategies.md).

## Sources

- W. H. Fleming, R. W. Rishel, *Deterministic and Stochastic Optimal Control*, Springer (1975), Chapter III, Theorem 4.1 (existence) and Theorem 5.1 (maximum principle), <https://doi.org/10.1007/978-1-4612-6380-7>.
- S. Lenhart, J. T. Workman, *Optimal Control Applied to Biological Models*, Chapman & Hall/CRC (2007), Chapters 1–4.
- J. K. K. Asamoah, M. A. Owusu, Z. Jin, F. T. Oduro, A. Abidemi, E. O. Gyasi, "Global stability and cost-effectiveness analysis of COVID-19 considering the impact of the environment: using data from Ghana", Chaos, Solitons & Fractals 140 (2020) 110103, Section 4 (objective functional (19), constrained system (20), existence conditions and Hamiltonian), <https://doi.org/10.1016/j.chaos.2020.110103> (PMC7351453).
- M. L. Diagne, H. Rwezaura, S. Y. Tchoumi, J. M. Tchuenche, "A Mathematical Model of COVID-19 with Vaccination and Treatment", Computational and Mathematical Methods in Medicine 2021 (2021) 1250129, Section 4 (objective (28), Hamiltonian (30), Theorem 2 with adjoint system (31) and control characterization), <https://doi.org/10.1155/2021/1250129>.
- A. Omame, H. Rwezaura, M. L. Diagne, S. C. Inyama, J. M. Tchuenche, "COVID-19 and dengue co-infection in Brazil: optimal control and cost-effectiveness analysis", The European Physical Journal Plus 136 (2021) 1090, Section 5 (Theorem 5.1), <https://doi.org/10.1140/epjp/s13360-021-02030-6>.
- O. Agossou, M. N. Atchadé, A. M. Djibril, "Modeling the effects of preventive measures and vaccination on the COVID-19 spread in Benin Republic with optimal control", Results in Physics (2021) 104969, Theorems 3–4, <https://doi.org/10.1016/j.rinp.2021.104969>.
- S. Ullah, M. A. Khan, "Modeling the impact of non-pharmaceutical interventions on the dynamics of novel coronavirus with optimal control analysis with a case study", Chaos, Solitons & Fractals (2020), Section 7 and Theorem 3 (adjoint system Eq. 18, control characterization Eq. 19), <https://doi.org/10.1016/j.chaos.2020.110075> (PMC7341999).
- M. M. Ojo, T. O. Benson, O. J. Peter, E. F. D. Goufo, "Nonlinear optimal control strategies for a mathematical model of COVID-19 and influenza co-infection", Physica A (2022), adjoint system, transversality conditions and control characterization (Eqs. 37–39), <https://doi.org/10.1016/j.physa.2022.128173> (PMC9461290).
- J. M. Tchuenche, N. Dube, C. P. Bhunu, R. J. Smith, C. T. Bauch, "The impact of media coverage on the transmission dynamics of human influenza", BMC Public Health 11 (Suppl 1) (2011) S5, Theorem 3 and the control characterization, <https://doi.org/10.1186/1471-2458-11-s1-s5> (PMC3317585).
- S. Y. Tchoumi, M. L. Diagne, H. Rwezaura, J. M. Tchuenche, "Malaria and COVID-19 co-dynamics: A mathematical model and optimal control", Applied Mathematical Modelling 99 (2021), objective (29), adjoint system (31) and control characterization, <https://doi.org/10.1016/j.apm.2021.06.016> (PMC8249695).
- A. Omame, M. Abbas, C. P. Onyenegecha, "Backward bifurcation and optimal control in a co-infection model for SARS-CoV-2 and ZIKV", Results in Physics 37 (2022) 105481, Eqs. (16)–(18), <https://doi.org/10.1016/j.rinp.2022.105481> (PMC8994284).
