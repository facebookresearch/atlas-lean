# With $p \ge 1$, $S$ does not determine a confounded batch effect

Let $p \ge 1$, fix $E \in \mathbb{R}^{n \times p}$, $\mu \in \mathbb{R}^p$ and $b \in \mathbb{R}^n$,
and write $X(\beta, \delta) = E + \mathbf 1 \mu^\top + b \beta^\top + b \delta^\top$ for the
confounded [additive design](batch-model.md), with batch effect $\beta$ and biological signal
$\delta$ attached to the same covariate $b$. Let $S(Y)$ be the
[sample covariance matrix](../principal-component-analysis/sample-cov.md)
of a data matrix $Y$. There is no map $f$ from real $p \times p$ matrices to $\mathbb{R}^p$ with

$$f\bigl(S(X(\beta, \delta))\bigr) = \beta \quad \text{for all } \beta, \delta \in \mathbb{R}^p.$$

Indeed, for every $a \in \mathbb{R}^p$, "all batch", $(\beta, \delta) = (a, 0)$, and "all biology",
$(\beta, \delta) = (0, a)$, give the same $S$, so $f$ would return both $a$ and $0$; some $a \ne 0$
exists since $p \ge 1$. This holds for every $n$, every residual matrix $E$, every baseline $\mu$
and every covariate $b$.

Compare the
[non-identifiability of the condition effect](../random-intercept-models-and-the-design-effect/not-identifiable-of-confounded.md)
under perfect confounding in the cell-level pseudobulk model, a statement about the probability law
of the data rather than about the sample covariance matrix.
