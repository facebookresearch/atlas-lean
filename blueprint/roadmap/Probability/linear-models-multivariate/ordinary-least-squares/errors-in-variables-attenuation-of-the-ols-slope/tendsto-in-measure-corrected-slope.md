# Consistency in probability of the corrected slope

Let $(\Omega, \mu)$ be a probability space and $\xi_i, u_i, \varepsilon_i$ ($i \ge 0$) real random variables satisfying the classical errors-in-variables hypotheses: the triples $(\xi_i, u_i, \varepsilon_i)$ are pairwise independent across $i$ and identically distributed, $\xi_0, u_0, \varepsilon_0$ are square integrable, and they are pairwise uncorrelated. Let $\beta_0, \beta \in \mathbb{R}$, and observe $x_i = \xi_i + u_i$ and $y_i = \beta_0 + \beta\,\xi_i + \varepsilon_i$. Write $\sigma_\xi^2 = \operatorname{Var}(\xi_0)$ and $\sigma_u^2 = \operatorname{Var}(u_0)$, and for the first $n$ observations $S_{xy} = \sum_{i<n} (x_i - \bar x)(y_i - \bar y)$ and $S_{xx} = \sum_{i<n} (x_i - \bar x)^2$. Let $\hat\sigma_{u,n}^2$ be almost everywhere strongly measurable real random variables converging in probability to $\sigma_u^2$. If $\sigma_\xi^2 \neq 0$, then

$$\frac{S_{xy}}{S_{xx} - n\,\hat\sigma_{u,n}^2} \longrightarrow \beta$$

in probability, with a quotient by $0$ taken to be $0$.
