# Slow rate for the Lasso prediction error, constant 3

Let $y = X\theta^* + w$, let $\lambda \ge 2\|X^\top w / n\|_\infty$, and let $\hat\theta$ have
Lagrangian Lasso objective at most that of $\theta^*$. Then

$$\frac1n \|X(\hat\theta - \theta^*)\|_2^2 \le 3\lambda \|\theta^*\|_1.$$

No sparsity of $\theta^*$ and no condition on $X$ is needed. This sharpens the constant $12$ of
the source's Theorem 11.2(a): the source's modified basic inequality (11.21),
with Hölder's inequality and the triangle inequality
$\|\Delta\|_1 \le \|\hat\theta\|_1 + \|\theta^*\|_1$, gives the constant $3$. The source's proof
first bounds $\|\Delta\|_1 \le 4\|\theta^*\|_1$ and obtains its stated constant $12$.

## Sources

- T. Hastie, R. Tibshirani and M. J. Wainwright, *Statistical Learning with Sparsity: The Lasso and Generalizations*, CRC Press, 2015: <https://hastie.su.domains/StatLearnSparsity/>, Theorem 11.2(a), inequality (11.21) and its proof.
