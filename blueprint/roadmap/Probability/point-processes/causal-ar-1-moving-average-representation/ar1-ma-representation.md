# Causal moving-average representation of an AR(1) process

Let $(\varepsilon_t)_{t \in \mathbb{Z}}$ be i.i.d. square-integrable random variables with mean $0$ on a probability space, and let $|\rho| < 1$. Then for every $t$: almost surely the series $\sum_{k \ge 0} \rho^k \varepsilon_{t-k}$ is summable; its sum $X_t$ satisfies the AR(1) recursion $X_t = \rho X_{t-1} + \varepsilon_t$ almost surely; $\mathbb{E}[X_t] = 0$; and $\operatorname{Var}(X_t) = \operatorname{Var}(\varepsilon_0)/(1 - \rho^2)$.
