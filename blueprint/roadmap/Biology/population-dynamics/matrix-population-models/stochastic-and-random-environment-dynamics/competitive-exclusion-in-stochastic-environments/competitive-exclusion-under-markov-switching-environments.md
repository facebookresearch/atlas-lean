# Competitive exclusion and its failure under Markov-switching environments

Let $r(t)$ be a continuous-time Markov chain on $\mathcal{N} = \{1, \dots, N\}$ with irreducible generator $Q = (q_{uv})$ and invariant probability measure $\nu$. Between switches, $n$ species follow the deterministic resource-competition dynamics of the current environment $u = r(t)$:

$$\frac{dx_i}{dt} = x_i\Big(-\alpha_i(r(t)) + \sum_{j=1}^m b_{ij}(r(t))\, R_j(x(t), r(t))\Big), \qquad i = 1, \dots, n.$$

The pair $(x(t), r(t))$ is a piecewise deterministic Markov process.

**Theorem (exclusion).** Suppose $m < n$, all resources eventually get exhausted, $\lim_{\|x\| \to \infty}\big(-\alpha_i(u) + \sum_j b_{ij}(u) R_j(x, u)\big) < 0$ for all $i$ and $u$, and there is one nonzero vector $c = (c_1, \dots, c_n)$ with $\sum_{i=1}^n c_i b_{ij}(u) = 0$ for all $j$ and simultaneously for all environments $u \in \mathcal{N}$. Then, with probability one, at least one species goes extinct, except possibly in the critical case $\sum_{i=1}^n c_i \sum_{k=1}^N \alpha_i(k)\nu_k = 0$.

**Theorem (coexistence by switching).** Take two species and one resource with linear consumption, so that in environment $u$

$$\frac{dx_i}{dt} = x_i\Big(-\alpha_i(u) + b_i(u)\big(\bar R(u) - a_1(u) x_1 - a_2(u) x_2\big)\Big),$$

a competitive Lotka-Volterra system in which one species excludes the other. There exist environments $E_1, E_2$ with the same maximal resource $\bar R(1) = \bar R(2)$, such that either species 1 wins in both, or species 1 wins in $E_1$ and species 2 wins in $E_2$, together with rates $q_{12}, q_{21} > 0$ for which both invasion rates of the switched system are positive. Consequently the joint process $(x(t), r(t))$ has a unique invariant probability measure $\Pi$ on $[0, \infty)^2 \times \{1, 2\}$ giving full mass to $(0, \infty)^2 \times \{1, 2\}$, and from every initial state in $(0, \infty)^2 \times \{1, 2\}$ the empirical occupation measures of $(x(t), r(t))$ converge weakly to $\Pi$ almost surely. The population marginal of $\Pi$ is concentrated on a compact set and gives full mass to $(0, \infty)^2$; its topological support may still meet the axes, since arbitrarily long intervals without switching bring the losing population arbitrarily close to zero. In particular, since $\{\min_i x_i > \eta\}$ is open, almost surely $\liminf_{t\to\infty} t^{-1}\int_0^t \mathbf 1\{\min_i x_i(s) > \eta\}\,ds \ge \Pi(\min_i x_i > \eta)$, which tends to $1$ as $\eta \to 0$: both species persist, and competitive exclusion fails.

## Expansion

For the exclusion theorem the common vector $c$ kills the resource terms in every environment at once: $\frac{d}{dt}\sum_i c_i \ln x_i = -\sum_i c_i \alpha_i(r(t))$, and by the ergodic theorem for $r$ the time average of the right side converges to $-\sum_i c_i \sum_k \alpha_i(k)\nu_k$, which is nonzero outside the critical case. If the null vectors differ across environments no such cancellation exists, and the second theorem shows the gap is real: spending time in both environments gives each species a positive invasion rate against the other's stationary distribution (a rescue effect), even when the same species wins in both fixed environments. That result follows from the persistence theory for PDMPs of Benaïm and Lobry (2016): positive invasion rates, computed in Appendix E of the source by an explicit integral formula and checked numerically for the examples of its Figures 3 and 4, give the unique interior invariant law and almost-sure convergence of occupation measures. The constant-environment counterpart, in which a common null vector always exists because the coefficients do not switch, is [competitive exclusion under linear white noise](stochastic-competitive-exclusion-with-linear-white-noise.md); it is a comparison, not a prerequisite. For fast switching the dynamics approach the averaged ODE with rates $\sum_u \nu_u(\cdot)$.

## Sources

- A. Hening and D. H. Nguyen, The competitive exclusion principle in stochastic environments, *J. Math. Biol.* 80 (2020), 1323–1351, <https://doi.org/10.1007/s00285-019-01464-y>; preprint arXiv:1810.00954. Locators follow the preprint: Section 5, equations (5.1)-(5.7), Theorems 5.1 and 5.2, Appendices D-E.
- M. Benaïm and C. Lobry, Lotka–Volterra with randomly fluctuating environments or "How switching between beneficial environments can make survival harder", *Ann. Appl. Probab.* 26 (2016), 3754–3785, <https://doi.org/10.1214/16-AAP1192>.
