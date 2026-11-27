# Monotone explicit schemes as convex combinations (discrete maximum principle)

Nonnegativity and the convex-combination form of the explicit (FTCS) heat step, and nonnegativity and the
sum identity of the first-order upwind step, are separate results and are not part of this node. This node
collects the remaining clauses.

## Expansion

A sound expansion has separate pages for:

1. **General convex-combination principle.** If $q^{n+1}_j = \sum_k c_k q^n_{j+k}$ with finitely many $c_k \ge 0$ and
   $\sum_k c_k = 1$, then $\inf_i q^n_i \le q^{n+1}_j \le \sup_i q^n_i$ for every $j$ (on a finite grid these are the
   minimum and maximum; on an infinite grid they are the infimum and supremum of bounded data); on a periodic grid
   the total $\sum_j q^{n+1}_j$ equals $\sum_j q^n_j$.
2. **Discrete maximum principle for the heat equation.** For the $\theta$-scheme on a finite grid with mesh ratio
   $\mu = \Delta t/\Delta x^2 \ge 0$ (diffusion coefficient normalized to one), $0 \le \theta \le 1$ and
   $\mu(1 - \theta) \le 1/2$, the numerical solution of the Dirichlet initial-boundary-value problem lies between the
   minimum and maximum of its initial and boundary values; the explicit scheme is the case $\theta = 0$, $\mu \le 1/2$.
3. **Unstable mode.** For the explicit heat scheme $q^{n+1}_j = q^n_j + \mu(q^n_{j+1} - 2q^n_j + q^n_{j-1})$ on the infinite
   grid, or on a periodic grid with an even number of points, the alternating mode $q_j = (-1)^j$ is multiplied by
   $1 - 4\mu$ in each step, so its amplitude grows when $\mu > 1/2$.

## Sources

- E. Süli, *Numerical Solution of Partial Differential Equations*, lecture slides, University of
  Oxford, 2022, Lecture 11: discrete maximum principle for the $\theta$-scheme under
  $\mu(1-\theta) \le 1/2$.
  <https://courses.maths.ox.ac.uk/pluginfile.php/25969/mod_resource/content/3/Lecture11.pdf>
