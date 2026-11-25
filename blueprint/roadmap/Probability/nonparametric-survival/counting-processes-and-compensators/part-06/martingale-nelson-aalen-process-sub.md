# Nelson–Aalen martingale

Consider Aalen's model in discrete time: a counting process $N$, a predictable at-risk process $Y$ with values in $\{0\} \cup [1, \infty)$ and a deterministic cumulative hazard $\alpha$, such that $N - Y \bullet \alpha$ is a martingale, with $\hat A = Y^{-1} \bullet N$ the Nelson–Aalen process (steps with $Y = 0$ contribute $0$) and $\Lambda^* = \mathbf 1\{Y \ne 0\} \bullet \alpha$ the restricted hazard. On a finite measure space, $\hat A - \Lambda^*$ is a martingale.
