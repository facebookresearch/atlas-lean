# Global boundedness with porous-medium diffusion and singular sensitivity

**Model.** On a smoothly bounded domain $\Omega \subset \mathbb{R}^n$, $n \ge 2$ (convex if $n \ge 3$), with no-flux (homogeneous Neumann) boundary conditions, consider the chemotaxis system

$$u_t = \nabla\cdot\big((u+a)^{m-1}\nabla u\big) - \chi\nabla\cdot\Big(u\frac{\nabla v}{v^k}\Big), \qquad v_t = \Delta v - v + u,$$

with $\chi, a, k > 0$ and $m > 1$: porous-medium-type diffusion of the cells and a singular (Weber-Fechner type for $k = 1$) sensitivity $\chi/v^k$ to the signal.

**Theorem.** Assume one of
- (A) $n = 2$, $k \in (0,\infty)$, $m > 1$;
- (B) $n \ge 3$, $k \in (0,\tfrac12)$, $m > 1 + \frac{(1-k)(n-2)}{n}$;
- (C) $n \ge 3$, $k \in [\tfrac12,1)$, $m > \frac{3n-2}{2n}$;
- (D) $n \ge 3$, $k \in [1,\infty)$, $m > \max\{1, \frac{3n-2}{2n+2}\}$.

Then for initial data $u_0 \in C^0(\overline{\Omega})$ nonnegative with $\int_\Omega u_0 > 0$ and $v_0 \in W^{1,\infty}(\Omega)$ with $v_0 > 0$ in $\overline{\Omega}$, the system has a unique global classical positive solution $(u,v) \in \big(C^0(\overline{\Omega}\times[0,\infty)) \cap C^{2,1}(\overline{\Omega}\times(0,\infty))\big)^2$, and it is uniformly bounded in time: $\sup_{t>0}\big(\|u(\cdot,t)\|_{L^\infty(\Omega)} + \|v(\cdot,t)\|_{W^{1,\infty}(\Omega)}\big) < \infty$.

In particular, in dimension three every $\chi > 0$, $a > 0$, $m > 1$ and $k \ge 1$ gives a global bounded solution, with no smallness condition on $\chi$.

## Expansion

With linear diffusion ($m = 1$) and $k \ge 1$, earlier three-dimensional boundedness results require $\chi$ to be small, because the drift $\chi u\nabla v/v^k$ is strongest where the signal is small. Two ingredients remove this: the signal stays bounded away from zero on bounded time intervals (it is produced by the cells, whose mass is conserved), and the diffusion $(u+a)^{m-1}\nabla u$ grows superlinearly in $u$, so in $L^p$-type energy estimates its dissipation dominates the cross-diffusive term once $m$ exceeds the dimension- and $k$-dependent thresholds above. Bounds in $L^p$ for large $p$ then upgrade to $L^\infty$ bounds and global classical solvability. The thresholds are compared in the source with those known for the parabolic-elliptic variant $0 = \Delta v - v + u$.

## Sources

- Minh Le, "Boundedness in a chemotaxis system with nonlinear diffusion and singular sensitivity", arXiv:2610.39507 (2026), Section 1, Theorem 1.1, <https://doi.org/10.48550/arXiv.2610.39507>.
