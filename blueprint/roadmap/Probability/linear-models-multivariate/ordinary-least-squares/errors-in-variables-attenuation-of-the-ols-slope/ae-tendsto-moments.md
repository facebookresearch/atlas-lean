# Almost sure limits of the observed sample moments

Let $(\Omega, \mu)$ be a probability space and $\xi_i, u_i, \varepsilon_i$ ($i \ge 0$) real random variables satisfying the classical errors-in-variables hypotheses: the triples $(\xi_i, u_i, \varepsilon_i)$ are pairwise independent across $i$ and identically distributed, $\xi_0, u_0, \varepsilon_0$ are square integrable, and they are pairwise uncorrelated. Let $\beta_0, \beta \in \mathbb{R}$, and observe $x_i = \xi_i + u_i$ and $y_i = \beta_0 + \beta\,\xi_i + \varepsilon_i$. Write $\sigma_\xi^2 = \operatorname{Var}(\xi_0)$ and $\sigma_u^2 = \operatorname{Var}(u_0)$, and for the first $n$ observations $S_{xy} = \sum_{i<n} (x_i - \bar x)(y_i - \bar y)$ and $S_{xx} = \sum_{i<n} (x_i - \bar x)^2$. Then, almost surely,

$$\frac{S_{xy}}{n} \longrightarrow \beta\,\sigma_\xi^2 \quad\text{and}\quad \frac{S_{xx}}{n} \longrightarrow \sigma_\xi^2 + \sigma_u^2 \qquad (n \to \infty).$$
