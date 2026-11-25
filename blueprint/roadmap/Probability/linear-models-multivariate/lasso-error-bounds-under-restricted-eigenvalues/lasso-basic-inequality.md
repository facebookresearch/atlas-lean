# Basic inequality for the Lagrangian Lasso

Let $y = X\theta^* + w$ with $\theta^*$ vanishing off $S$, let $\lambda > 0$ with
$\lambda \ge 2\|X^\top w / n\|_\infty$, and let $\hat\theta$ have Lasso objective at most that
of $\theta^*$ (for example a minimiser). Then the error $\Delta = \hat\theta - \theta^*$
satisfies

$$\Delta \in \mathcal{C}(S; 3) \quad \text{and} \quad \frac1n \|X\Delta\|_2^2 \le 3\lambda \|\Delta_S\|_1.$$

The statement is deterministic: it holds for every noise vector $w$.

## Sources

- T. Hastie, R. Tibshirani and M. J. Wainwright, *Statistical Learning with Sparsity: The Lasso and Generalizations*, CRC Press, 2015: <https://hastie.su.domains/StatLearnSparsity/>, Lemma 11.1 and inequality (11.23).
- M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University Press, 2019, §7.3.
