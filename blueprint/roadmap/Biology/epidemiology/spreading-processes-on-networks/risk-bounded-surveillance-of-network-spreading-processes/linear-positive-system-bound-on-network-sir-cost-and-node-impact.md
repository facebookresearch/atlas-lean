# Linear positive-system bound on network SIR cost and node impact

Let $\mathcal{G}$ be a directed network on $n$ nodes with edge set $\mathcal{E}$, spreading rates $\beta_{ij} \ge 0$ for $(i,j) \in \mathcal{E}$ and recovery rates $\delta_i \ge 0$. Let $X_i(t) \in \{0,1\}$ indicate that node $i$ is infected in the stochastic network SIR process, and let $\chi_i(t)$, $z_i(t)$ solve the mean-field system

$$\dot\chi_i = (1 - \chi_i - z_i)\sum_{j=1}^n \beta_{ij}\chi_j - \delta_i \chi_i, \qquad \dot z_i = \delta_i \chi_i .$$

Let $A$ be the Metzler matrix with $a_{ii} = -\delta_i$, $a_{ij} = \beta_{ij}$ for $(i,j) \in \mathcal{E}$ and $a_{ij} = 0$ otherwise, and let $x$ solve the linearization $\dot x = A x$. For a non-negative row cost vector $C$ and discount rate $r \ge 0$ define the discounted costs

$$J_M = \int_0^\infty e^{-rt}\, C\, \mathbb{E}[X(t)]\,dt, \qquad J_L(x(0)) = \int_0^\infty e^{-rt}\, C\, x(t)\,dt .$$

**Theorem.**

1. (Comparison) If $\chi(0) = \mathbb{E}[X(0)]$ then $\chi_i(t) \ge \mathbb{E}[X_i(t)]$ for all $t \ge 0$; if $x(0) \ge \chi(0)$ then $x(t) \ge \chi(t)$ for all $t \ge 0$. Consequently, with $x(0) = \chi(0) = \mathbb{E}[X(0)]$,

$$\int_0^\infty e^{-rt} C x(t)\,dt \;\ge\; \int_0^\infty e^{-rt} C \chi(t)\,dt \;\ge\; J_M .$$

2. (Node impact) If $A - rI$ is Hurwitz, then $J_L(x(0)) = \sum_{i=1}^n p_i x_i(0)$ with the **node impact** vector

$$p^{\mathsf T} = C\,(rI - A)^{-1} \ge 0,$$

which is also the optimal solution of the linear program $\min \|p\|_1$ subject to $p \ge 0$, $p^{\mathsf T}A - r p^{\mathsf T} \le -C$; $p_i$ upper-bounds the expected discounted cost of an outbreak seeded at node $i$.
3. (Feasibility) If $C$ is entrywise positive, these constraints are feasible if and only if $A - rI$ is Hurwitz, i.e. the spectral abscissa satisfies $\lambda_{\max}(A) < r$; minimizing the admissible discount rate is therefore an upper-bound surrogate for minimizing $\lambda_{\max}(A)$. (The source's Corollary 1 states this for non-negative $C$, where it fails: $C = 0$, $p = 0$ is feasible for every $A$.)

## Expansion

The factor $1 - \chi_i - z_i \in [0,1]$ multiplying the infection pressure is dropped in the linearization, and because $A$ is Metzler the flow of $\dot x = Ax$ is order-preserving, giving $x \ge \chi$; the moment closure behind $\chi \ge \mathbb{E}[X]$ uses positive correlation of infection indicators. Integrating $e^{-rt} C e^{At} x(0)$ gives $C(rI - A)^{-1}x(0)$ whenever $A - rI$ is Hurwitz, and $(rI - A)^{-1} \ge 0$ for a Metzler $A$ with $\lambda_{\max}(A) < r$, so $p \ge 0$. The LP characterization is the dual (Lyapunov-type) certificate of positive systems: any feasible $p$ dominates $C(rI-A)^{-1}$ entrywise.

## Sources

- Vera L. J. Somers, Ian R. Manchester, "Minimizing the Risk of Spreading Processes via Surveillance Schedules and Sparse Control", IEEE Transactions on Control of Network Systems 10 (2023), 394–406, <https://doi.org/10.1109/tcns.2022.3203359>. Published version of arXiv:2107.05878, cited next; locators there refer to the arXiv version.
- Vera L. J. Somers, Ian R. Manchester, "Minimizing the Risk of Spreading Processes via Surveillance Schedules and Sparse Control", arXiv (2021). Equations (eq1)–(eq:epi), Lemmas 1–4, Corollary 1. <https://doi.org/10.48550/arXiv.2107.05878>
