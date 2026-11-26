# Reduced convex surrogate-data problem of optimal scaling

**Setting.** A mechanistic model with parameters $\theta$ produces simulated readouts $y(t_i, \theta)$, $i = 1, \dots, N$. The data are qualitative: observation $i$ belongs to category $C_{k(i)}$ of ordered categories $C_1 < \dots < C_K$. *Optimal scaling* introduces surrogate data $\tilde y_i$ and category bounds $l_k \le u_k$ by

$$(\tilde y, l, u)(\theta) = \arg\min_{\tilde y, l, u} \sum_{i=1}^{N} w_i\,(\tilde y_i - y(t_i, \theta))^2 \quad \text{s.t. } l_{k(i)} \le \tilde y_i \le u_{k(i)},\ \ u_k \le l_{k+1},$$

and estimates $\hat\theta = \arg\min_\theta \sum_i w_i (\tilde y_i(\theta) - y(t_i, \theta))^2$, which is zero exactly when the simulation reproduces the observed qualitative ordering. The weights $w_i$ normalize by the scale and variation of the simulation so that shrinking the simulation cannot trivially improve the fit.

**Surrogate data from bounds.** For given bounds the optimal surrogate is the projection $\tilde y_i = \min\{\max\{y(t_i, \theta), l_{k(i)}\}, u_{k(i)}\}$, so the bounds solve

$$\min_{l, u} \sum_{i=1}^{N} w_i \Bigl( \max\{0, l_{k(i)} - y(t_i, \theta)\}^2 + \max\{0, y(t_i, \theta) - u_{k(i)}\}^2 \Bigr) \quad \text{s.t. } l_k \le u_k,\ u_k \le l_{k+1}.$$

**Lemma.** This problem has an optimal solution with no gaps between adjacent categories, $u_k^* = l_{k+1}^*$ for $k = 1, \dots, K-1$.

**Theorem (reduction).** An optimal solution is obtained by solving

$$u(\theta) = \arg\min_{u} \sum_{i=1}^{N} w_i \Bigl( \max\{0, u_{k(i)-1} - y(t_i, \theta)\}^2 + \max\{0, y(t_i, \theta) - u_{k(i)}\}^2 \Bigr) \quad \text{s.t. } u_k \le u_{k+1},$$

with $u_0 = \min_i y(t_i, \theta)$, $u_K = \max_i y(t_i, \theta)$, and setting $l_{k+1} = u_k$; this has $K - 1$ variables instead of about $2K$. Substituting $u_k = u_0 + \sum_{k' \le k} d_{k'}$ turns the order constraints into $d_k \ge 0$. With a required minimal gap $g$ and minimal category size $s$, the same holds with $l_{k+1} = u_k + g$ and constraints $u_k + g + s \le u_{k+1}$.

**Theorem (convexity).** The bound problem, the reduced problem and its difference reformulation (and their versions with gap and size constraints) are convex optimization problems.

## Expansion

If an optimal solution had a gap $u_{k} < l_{k+1}$, every observation in category $k$ would lie strictly below $u_k$ (else raising $u_k$ to $l_{k+1}$ would lower the objective), and lowering $l_{k+1}$ to $u_k$ can only reduce penalties for category $k+1$; so closing gaps never hurts, which is the lemma. The reduced problem is the original restricted to the subspace $l_{k+1} = u_k$, which contains an optimum. Each summand $\max\{0, \cdot\}^2$ of an affine function of the bounds is convex, sums preserve convexity, and the constraints are linear, so any local optimizer finds a global optimum of the inner problem. The box-constrained difference form allows standard bound-constrained solvers, which in benchmarks made the nested inner optimization substantially faster and more robust than the original formulation.

## Sources

- L. Schmiester, D. Weindl, J. Hasenauer, "Parameterization of mechanistic models from qualitative data using an efficient optimal scaling approach", Journal of Mathematical Biology (2020), Section 2 (optimal scaling, Eqs. 5–10), Lemma 1, Theorem 1 (reduced problem, Eq. 11), difference reformulation (Eq. 12), Theorem 2 (convexity), Theorem 3 (gap and size constraints, Eqs. 13–14). <https://doi.org/10.1007/s00285-020-01522-w> (PMC7427713).
