# Slow rate for the Lasso prediction error

Let $y = X\theta^* + w$ with $\|\theta^*\|_1 \le R_1$, and let $\lambda \ge 0$ with
$\lambda \ge 2\|X^\top w / n\|_\infty$. Then every minimiser $\hat\theta$ of the Lagrangian Lasso
objective satisfies

$$\frac1n \|X(\hat\theta - \theta^*)\|_2^2 \le 12 R_1 \lambda.$$

With $\lambda \asymp \sigma\sqrt{\log d / n}$ the squared prediction error decays like
$1/\sqrt{n}$, hence the name "slow rate".

## Sources

- T. Hastie, R. Tibshirani and M. J. Wainwright, *Statistical Learning with Sparsity: The Lasso and Generalizations*, CRC Press, 2015: <https://hastie.su.domains/StatLearnSparsity/>, Theorem 11.2(a).

## Background

- [Fast rate for the Lasso prediction error](lasso-prediction-error-le-fast.md): the $1/n$ rate under sparsity and a restricted eigenvalue condition.
