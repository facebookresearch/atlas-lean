# With $p \ge 1$, $S$ does not determine a confounded biological signal

Let $p \ge 1$, fix $E \in \mathbb{R}^{n \times p}$, $\mu \in \mathbb{R}^p$ and $b \in \mathbb{R}^n$,
and write $X(\beta, \delta) = E + \mathbf 1 \mu^\top + b \beta^\top + b \delta^\top$ for the
confounded [additive design](batch-model.md), with batch effect $\beta$ and biological signal
$\delta$ attached to the same covariate $b$. Let $S(Y)$ be the
[sample covariance matrix](../principal-component-analysis/sample-cov.md)
of a data matrix $Y$. There is no map $f$ from real $p \times p$ matrices to $\mathbb{R}^p$ with

$$f\bigl(S(X(\beta, \delta))\bigr) = \delta \quad \text{for all } \beta, \delta \in \mathbb{R}^p.$$

Indeed, for every $a \in \mathbb{R}^p$, $(\beta, \delta) = (0, a)$ and $(\beta, \delta) = (a, 0)$
give the same $S$, so $f$ would return both $a$ and $0$; some $a \ne 0$ exists since $p \ge 1$. This
holds for every $n$, every residual matrix $E$, every baseline $\mu$ and every covariate $b$.
