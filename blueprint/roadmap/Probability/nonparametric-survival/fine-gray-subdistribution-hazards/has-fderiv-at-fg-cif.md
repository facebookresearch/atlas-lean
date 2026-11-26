# Differentiability of the Fine–Gray cumulative-incidence map

For a scalar covariate value $x$, coefficient $b$ and baseline cumulative subdistribution hazards $\Lambda_j$ on a grid, let $F_j(b, \Lambda) = 1 - \exp(-e^{bx}\Lambda_j)$ and $s_j = (1 - F_j)e^{bx}$. On a finite grid, $(b, \Lambda) \mapsto F(b, \Lambda)$ is Fréchet differentiable with derivative $(h, H) \mapsto (s_j(x\Lambda_jh + H_j))_j$.
