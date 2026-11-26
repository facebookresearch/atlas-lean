# Consistency of the corrected slope with known measurement-error variance

Let $(\Omega, \mu)$ be a probability space and $\xi_i, u_i, \varepsilon_i$ ($i \ge 0$) real random variables satisfying the classical errors-in-variables hypotheses: the triples $(\xi_i, u_i, \varepsilon_i)$ are pairwise independent across $i$ and identically distributed, $\xi_0, u_0, \varepsilon_0$ are square integrable, and they are pairwise uncorrelated. Let $\beta_0, \beta \in \mathbb{R}$, and observe $x_i = \xi_i + u_i$ and $y_i = \beta_0 + \beta\,\xi_i + \varepsilon_i$. Write $\sigma_\xi^2 = \operatorname{Var}(\xi_0)$ and $\sigma_u^2 = \operatorname{Var}(u_0)$, and for the first $n$ observations $S_{xy} = \sum_{i<n} (x_i - \bar x)(y_i - \bar y)$ and $S_{xx} = \sum_{i<n} (x_i - \bar x)^2$. If $\sigma_\xi^2 \neq 0$, then almost surely

$$\frac{S_{xy}}{S_{xx} - n\,\sigma_u^2} \longrightarrow \beta \qquad (n \to \infty),$$

with a quotient by $0$ taken to be $0$.
