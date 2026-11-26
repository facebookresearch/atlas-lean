# Global well-posedness of stochastic two-species chemotaxis-competition

**Model.** Two competing species $u$, $v$ both produce and follow a common signal $w$, under multiplicative noise, on a bounded smooth domain $\mathcal{O} \subset \mathbb{R}^n$, $n \in \{1,2\}$, with homogeneous Neumann conditions:

$$\begin{aligned}
du &= \big[\Delta u - \chi_1\nabla\cdot(u\nabla w) + \mu_1u(1 - u^{\zeta_1} - a_1v^{\eta_1})\big]dt + \sigma_1(u)\,dW_1,\\
dv &= \big[\Delta v - \chi_2\nabla\cdot(v\nabla w) + \mu_2v(1 - v^{\zeta_2} - a_2u^{\eta_2})\big]dt + \sigma_2(v)\,dW_2,\\
\partial_t w &= \Delta w - w + \alpha u + \beta v.
\end{aligned}$$

The noise coefficients are globally Lipschitz as $\ell^2$-valued maps, vanish at $0$ (no noise on an extinct species) and grow at most linearly; all deterministic coefficients are positive.

**Theorem.** Assume superquadratic self-damping and at least linear competition,
$$\zeta_1 > 2, \qquad \zeta_2 > 2, \qquad \eta_1 \ge 1, \qquad \eta_2 \ge 1,$$
and nonnegative $\mathcal{F}_0$-measurable initial data $u_0, v_0 \in C(\overline{\mathcal{O}})$, $w_0 \in W^{1,\infty}(\mathcal{O})$ with finite moments of all orders.
1. (Global solutions) There is a unique global adapted nonnegative mild solution, with $u, v \in L^1(\Omega; C([0,T]; C(\overline{\mathcal{O}})))$ and $w \in L^1(\Omega; C([0,T]; W^{1,q}(\mathcal{O})))$ for every $T > 0$, $q > n$.
2. (Continuous dependence) If initial data $X_{0,k} \to X_0$ in $L^p(\Omega;\mathcal{X}_q)$, $p \ge 2$, with the same coefficients and Wiener processes and uniformly bounded expected sup-norms, then $X_k \to X$ in probability in $C([0,T];\mathcal{X}_q)$.

## Expansion

Local solutions come from a cut-off system with truncated nonlinearities, solved by a fixed point in spaces of continuous functions; pathwise uniqueness up to stopping times makes the truncations consistent, and positivity holds because the noise vanishes at zero. Globality follows from the stopped $L^p$ Itô formula for $\|u\|_{L^p}^p$: the chemotactic cross term $p(p-1)\chi_1\int u^{p-1}\nabla u\cdot\nabla w$ and the competition and Itô correction terms have no fixed sign, but parabolic regularity for $w$ (driven by $\alpha u + \beta v$) bounds $\nabla w$, and the damping $-\mu_1\int u^{p+\zeta_1}$ with $\zeta_1 > 2$ dominates them, while stochastic convolution estimates handle the martingale parts. Uniform $L^p$ and then sup-norm bounds give $\tau_m \to \infty$.

## Sources

- Yiming Jiang, Haohang Li and Yawei Wei, "Stochastic Two-Species Chemotaxis Competition: Global Well Posedness and Continuous Dependence", arXiv:2608.04636 (2026), Section 2 (Assumption 2.4), Section 3 (Theorems 3.1-3.2), Section 4 (Assumption 4.1, Theorem 4.5) and Section 5 (Theorem 5.1), <https://doi.org/10.48550/arXiv.2608.04636>.
