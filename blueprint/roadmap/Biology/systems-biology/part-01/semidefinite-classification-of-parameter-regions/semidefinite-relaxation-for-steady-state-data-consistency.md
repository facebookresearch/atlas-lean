# Semidefinite relaxation for steady-state data consistency

**Problem.** For a mass-action model with concentrations $y \in \mathbb{R}^n$ and rate constants $k$, the steady-state conditions $f_i(k, y) = 0$ ($i = 1, \dots, n$) are polynomial in $y$ and affine in $k$. Measured totals $M y = b$ ($M \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$) are imposed with relative accuracy $\varepsilon$:

$$(1 - \varepsilon)\, b \le M y \le (1 + \varepsilon)\, b.$$

The parameter set $k$ is consistent with the data if some $y$ satisfies both.

**Lifting.** Put $x = (1, y) \in \mathbb{R}^{n+1}$ and $X = x x^{\mathsf T}$. When each steady-state equation is quadratic in $y$, it can be written $x^{\mathsf T} Q_i x = 0$ with a symmetric matrix $Q_i$ whose entries are affine in $k$, and the data bounds become $L x \ge 0$ (each row of $L$ prepends $\mp(1 \mp \varepsilon) b_j$ to a row of $\pm M$). The consistency problem is the nonconvex feasibility problem $x^{\mathsf T} Q_i x = 0$, $L x \ge 0$, $x_1 = 1$.

**Relaxation.** Dropping the rank-one condition $X = x x^{\mathsf T}$ gives the semidefinite program

$$\min_X \ \mathrm{Tr}(Q_{\mathrm{obj}} X) \quad \text{s.t.} \quad \mathrm{Tr}(Q_i X) = 0,\ \ X_{11} = 1,\ \ L X e_1 \ge 0,\ \ L X L^{\mathsf T} \ge 0,\ \ X \succeq 0,$$

with $Q_{\mathrm{obj}} = 0$ for pure feasibility; the redundant entrywise constraint $L X L^{\mathsf T} \ge 0$ (products of pairs of linear bounds) tightens the relaxation. Its dual is

$$\max\ \gamma \quad \text{s.t.} \quad Q_{\mathrm{obj}} \succeq \gamma\, e_1 e_1^{\mathsf T} + \sum_i \lambda_i Q_i + e_1 r^{\mathsf T} L + L^{\mathsf T} r\, e_1^{\mathsf T} + L^{\mathsf T} S L, \qquad r \ge 0,\ S \ge 0,\ S_{ii} = 0.$$

**Proposition.**

1. The feasible set of the relaxation is convex and contains $x x^{\mathsf T}$ for every consistent steady state $x = (1, y)$.
2. If the relaxation has a feasible solution of rank one, $X = x x^{\mathsf T}$ with $x_1 = 1$, then $y$ is a steady state consistent with the data.
3. (Infeasibility certificate.) For $Q_{\mathrm{obj}} = 0$, any dual feasible point with $\gamma > 0$ proves that the relaxation, and hence the original problem, is infeasible: the parameters $k$ are inconsistent with the data.

## Expansion

Items 1 and 2 are immediate from the lifting. For item 3, weak duality ($\mathrm{Tr}(C X) \ge b^{\mathsf T} z$ for any primal feasible $X$ and dual feasible $z$) applied here reads: if $X$ is primal feasible, take the trace of the dual matrix inequality against $X \succeq 0$ to get

$$0 \ge \gamma X_{11} + \sum_i \lambda_i \mathrm{Tr}(Q_i X) + 2 r^{\mathsf T} L X e_1 + \mathrm{Tr}\bigl(S\, L X L^{\mathsf T}\bigr) \ge \gamma,$$

since $\mathrm{Tr}(Q_i X) = 0$ and $r$, $S$, $L X e_1$, $L X L^{\mathsf T}$ are entrywise nonnegative. So $\gamma > 0$ is impossible when a primal point exists. A dual point is a solver-independent proof that no steady state matches the data.

The relaxation replaces root finding or long simulations by one small convex problem per parameter set. For the cycle $A + B \to A{\cdot}B \to A{\cdot}B^* \to A + B$ with the data $[A] = [B] = 1/3$, $[A{\cdot}B] + [A{\cdot}B^*] = 2/3$ at $\varepsilon = 20\%$ and $k = (3, 1, 1)$, the solver returns a rank-one $X$ whose scaled leading eigenvector is the steady state $([A], [B], [A{\cdot}B], [A{\cdot}B^*]) = (1/3, 1/3, 1/3, 1/3)$. Rank checks reject few solutions in practice. Since all constraints are linear in $k$, the set of consistent parameters is a cone.

## Sources

- L. Kuepfer, U. Sauer, P. A. Parrilo, "Efficient classification of complete parameter regions based on semidefinite programming", BMC Bioinformatics 8 (2007) 12, Equations 1 to 8 (steady state, data bounds, lifting, relaxation and dual), Equations 9 to 15 (worked example), the subsection on reducing rank failures, and the Appendix, Equations 16 and 17 (convex relaxation) and 18 to 20 (weak duality), <https://doi.org/10.1186/1471-2105-8-12>, PMCID PMC1800867.
