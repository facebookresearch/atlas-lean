# Ranking order of strategies and fitness reconstruction under clonal inheritance

**Setting.** Inherited strategies $v$ range over a compact subset of a metric space $V$ with a Borel measure; the abundance $\rho(v,t) \ge 0$ of strategy $v$ evolves as $\partial_t\rho(v,t) = F_v\big(\rho, t, \vec M(v)\big)$, where $\vec M(v) = (M_1(v), \dots, M_n(v))$ are life-history parameters (functions or functionals of $v$), the total population is uniformly bounded, and inheritance is clonal ($\rho(v, t_0) = 0$ implies $\rho(v,t) = 0$ for $t > t_0$).

**Ranking order.** Strategy $v$ is fitter than $w$, written $v \succ w$, if $\rho(w', t)/\rho(v', t) \to 0$ as $t \to \infty$ uniformly for $v'$, $w'$ in neighbourhoods of $v$, $w$. This relation is transitive and anti-reflexive, hence a partial order. If the long-run average per-capita rates

$$R_v = \lim_{T\to\infty}\frac1T\int_0^T \frac{\partial_t\rho(v,t)}{\rho(v,t)}\,dt$$

exist uniformly, then $R_v > R_w$ implies $v \succ w$ (the converse need not hold).

**Fitness and its reconstruction.** If the order does not depend on initial conditions and is represented by a function $Y(v) = J(\vec M(v))$ with $Y(v) > Y(w)$ whenever $v \succ w$, and $J$ is smooth, then near a reference point $J$ is approximated by

$$Y \approx \sum_i B_i M_i + \sum_{i \le j} C_{ij}M_iM_j .$$

Simulating the joint long-term dynamics of $N$ strategies near the optimum and ranking them by $R_1 > R_2 > \dots > R_N$ yields the $N - 1$ linear inequalities

$$\vec B\,(\vec M_{k+1} - \vec M_k) + \vec M_{k+1}C\vec M_{k+1}^{\top} - \vec M_k C \vec M_k^{\top} < 0, \qquad k = 1, \dots, N-1,$$

in the unknown coefficients (normalized, e.g. $B_1 = 1$), solvable by linear programming. The evolutionarily optimal strategy maximizes the fitted $Y$ over the feasible set, which for function-valued traits is typically attained on the boundary of the attainable parameter region.

## Expansion

Ranking only needs the sign of the long-run growth difference, so the method uses competition outcomes rather than an assumed optimization criterion; a quadratic $Y$ makes the final maximization over function-valued strategies (such as a daily depth trajectory of migrating zooplankton) semi-analytic. If too many strategies are ranked, the inequalities can become infeasible, signalling that the quadratic model of $Y$ is too crude on that region. The approach fails when the ranking depends on initial conditions (frequency-dependent selection), although special cases such as a single predator with competing prey strategies can still be handled.

## Sources

- S. K. Sandhu, A. Morozov, O. Kuzenkov, "Revealing evolutionarily optimal strategies in self-reproducing systems via a new computational approach", Bulletin of Mathematical Biology 81 (2019) 4701–4725, Sect. 2.1–2.2: Definition 1, Assumptions 1–3, equations (1)–(7), <https://doi.org/10.1007/s11538-019-00663-4>, PMCID: PMC6874526.
