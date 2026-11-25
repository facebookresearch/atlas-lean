# The optimal control-variate coefficient

Let $f(X)$ and $h(X)$ be square-integrable, and let the control variate $h(X)$ have known mean $\theta$. For a coefficient $\beta$ fixed in advance, $f(X) - \beta(h(X) - \theta)$ has mean $E[f(X)]$. If $\operatorname{Var}(h(X)) > 0$, its variance is a quadratic in $\beta$ with leading coefficient $\operatorname{Var}(h(X))$, so it has the unique minimizer $\beta_{\mathrm{opt}} = \operatorname{Cov}(f(X), h(X))/\operatorname{Var}(h(X))$ and minimum value $\operatorname{Var}(f(X)) - \operatorname{Cov}(f(X), h(X))^2/\operatorname{Var}(h(X))$; when moreover $\operatorname{Var}(f(X)) > 0$, this minimum equals $(1 - \rho^2)\operatorname{Var}(f(X))$ with $\rho = \operatorname{Corr}(f(X), h(X))$. If $\operatorname{Var}(h(X)) = 0$, then $h(X) = \theta$ almost surely, so $f(X) - \beta(h(X) - \theta) = f(X)$ almost surely for every $\beta$: the variance does not depend on $\beta$ and every $\beta$ minimizes it. If $\beta$ is estimated from the same sample, unbiasedness is no longer automatic. Antithetic and common-random-number comparisons need a sign condition on the relevant covariance and are separate.

## Sources

- A. B. Owen, *Monte Carlo Theory, Methods and Examples*, chapter 8 "Variance reduction", <https://artowen.su.domains/mc/>, §8.9
