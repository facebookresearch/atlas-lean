# Fast rate for the Lasso prediction error

Let $y = X\theta^* + w$ with $\theta^*$ vanishing off $S$, suppose that $X$ satisfies the
restricted eigenvalue condition with constant $\kappa$ over $\mathcal{C}(S; 3)$, and let
$\lambda > 0$ with $\lambda \ge 2\|X^\top w / n\|_\infty$. Then every minimiser $\hat\theta$ of
the Lagrangian Lasso objective satisfies

$$\frac1n \|X(\hat\theta - \theta^*)\|_2^2 \le \frac{9}{\kappa} |S| \lambda^2.$$

## Sources

- T. Hastie, R. Tibshirani and M. J. Wainwright, *Statistical Learning with Sparsity: The Lasso and Generalizations*, CRC Press, 2015: <https://hastie.su.domains/StatLearnSparsity/>, Theorem 11.2(b).

## Background

- [Slow rate for the Lasso prediction error](lasso-prediction-error-le-slow.md): the bound without sparsity or restricted eigenvalue assumptions.
