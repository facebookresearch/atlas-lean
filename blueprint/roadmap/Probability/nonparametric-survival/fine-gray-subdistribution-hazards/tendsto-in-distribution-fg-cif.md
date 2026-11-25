# Delta method for the Fine–Gray cumulative incidence

For a scalar covariate value $x$, coefficient $b$ and baseline cumulative subdistribution hazards $\Lambda_j$ on a grid, let $F_j(b, \Lambda) = 1 - \exp(-e^{bx}\Lambda_j)$ and $s_j = (1 - F_j)e^{bx}$. On a finite grid, if $\sqrt n((\hat\beta_n, \hat\Lambda_n) - (\beta_0, \Lambda_0)) \Rightarrow Z$, then $\sqrt n(F(\hat\beta_n, \hat\Lambda_n) - F(\beta_0, \Lambda_0)) \Rightarrow DF(\beta_0, \Lambda_0)Z$.
