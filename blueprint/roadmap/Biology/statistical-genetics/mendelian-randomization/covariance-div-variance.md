# Bias of the ordinary least-squares coefficient under confounding

Let $(Z, X, Y, U, \alpha, \beta)$ be a [linear moment model](linear-moment-model.md) on a probability measure $\mu$ with $\operatorname{Var}(X) \ne 0$. Then

$$\frac{\operatorname{Cov}(X, Y)}{\operatorname{Var}(X)} = \beta + \frac{\operatorname{Cov}(X, U)}{\operatorname{Var}(X)},$$

so the regression coefficient of $Y$ on $X$ differs from $\beta$ exactly when $\operatorname{Cov}(X, U) \ne 0$.
