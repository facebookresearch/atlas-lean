# Generalized estimating equations for clustered data

Observe $K$ independent clusters (subjects); cluster $i$ has an outcome vector $Y_i = (y_{i1}, \dots, y_{in_i})^\top$ and covariate vectors $x_{it} \in \mathbb{R}^p$. Only the first two marginal moments are modelled:

$$\mathbb{E}[y_{it}] = \mu_{it} = h(x_{it}^\top \beta), \qquad \operatorname{Var}(y_{it}) = \phi\, v(\mu_{it}),$$

with a known inverse link $h$, a known variance function $v$, a regression parameter $\beta \in \mathbb{R}^p$ and a scale $\phi > 0$, as in a generalized linear model. The dependence within a cluster is described by a working correlation matrix $R_i(\alpha)$ ($n_i \times n_i$, depending on a finite-dimensional parameter $\alpha$), giving the working covariance

$$V_i = \phi\, A_i^{1/2} R_i(\alpha) A_i^{1/2}, \qquad A_i = \operatorname{diag}\bigl(v(\mu_{i1}), \dots, v(\mu_{in_i})\bigr).$$

With $\mu_i(\beta) = (\mu_{i1}, \dots, \mu_{in_i})^\top$ and $D_i = \partial \mu_i / \partial \beta^\top$ ($n_i \times p$), the generalized estimating equation (GEE) estimator $\hat\beta$ solves

$$U(\beta) = \sum_{i=1}^K D_i^\top V_i^{-1} \bigl(Y_i - \mu_i(\beta)\bigr) = 0,$$

where $\alpha$ and $\phi$ are replaced by estimates $\hat\alpha(\beta), \hat\phi(\beta)$ computed from Pearson residuals $(y_{it} - \mu_{it}) / v(\mu_{it})^{1/2}$.

When $R_i = I$ the equation is the independence (quasi-likelihood) score of an ordinary generalized linear model; when $n_i = 1$ for all $i$ it reduces to the usual quasi-likelihood equation.

## Expansion

$U$ is unbiased, $\mathbb{E}\,U(\beta) = 0$ at the true $\beta$, using only the mean model; the working correlation enters only as a weight. A common iteration is Fisher scoring, $\beta \leftarrow \beta + \bigl(\sum_i D_i^\top V_i^{-1} D_i\bigr)^{-1} \sum_i D_i^\top V_i^{-1}(Y_i - \mu_i)$, alternated with moment updates of $\alpha$ and $\phi$. Common choices of $R(\alpha)$ are independence, exchangeable, first-order autoregressive and unstructured.

## Sources

- K.-Y. Liang and S. L. Zeger, "Longitudinal data analysis using generalized linear models", Biometrika 73 (1986), 13–22, <https://doi.org/10.1093/biomet/73.1.13>.
