# Beta is the least-squares slope

Let $X$ and $Y$ be square-integrable random variables with $\operatorname{Var}(Y) > 0$. The function $(a, b) \mapsto E[(X - a - bY)^2]$ has the unique minimizer $b = \operatorname{Cov}(X, Y)/\operatorname{Var}(Y)$, $a = E[X] - bE[Y]$. So the beta of a return $X$ relative to a market return $Y$ is the slope of the least-squares regression of $X$ on $Y$.

Proof. For fixed $b$ the minimizing $a$ is $E[X - bY]$, leaving $\operatorname{Var}(X - bY) = \operatorname{Var}(X) - 2b\operatorname{Cov}(X, Y) + b^2\operatorname{Var}(Y)$, a strictly convex quadratic in $b$ minimized at $\operatorname{Cov}(X, Y)/\operatorname{Var}(Y)$.

## Depends on

- [Beta of a return relative to the market return](asset-beta.md): the beta of a return relative to the market return.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
