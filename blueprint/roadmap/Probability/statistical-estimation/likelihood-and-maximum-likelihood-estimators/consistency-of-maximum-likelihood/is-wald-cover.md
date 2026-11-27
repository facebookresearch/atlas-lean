# Wald cover of a parameter set

For a log-likelihood $\ell_\theta(x)$, $\theta$ in a pseudometric space, and observations $X_0, X_1, \dots$ on a measure space with measure $P$ (expectations are integrals against $P$), write $Q(\theta) = \mathbb{E}[\ell_\theta(X_0)]$. A Wald cover of a set $S$ away from $\theta_0$ at radius $\varepsilon$ is a finite family of pairs $(B, u)$ whose sets $B$ cover $S \setminus B(\theta_0, \varepsilon)$, where each $u$ is measurable with $u(X_0)$ integrable, $\ell_\theta \le u$ for every $\theta \in B$, and $\mathbb{E}[u(X_0)] < Q(\theta_0)$.
