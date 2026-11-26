# $\ell_2$-error bound for the constrained Lasso

Let $y = X\theta^* + w$ with $\theta^*$ vanishing off a set $S$ of $s$ coordinates, and suppose
that $X$ satisfies the restricted eigenvalue condition with constant $\kappa$ over
$\mathcal{C}(S; 1)$. Then every minimiser $\hat\theta$ of $\frac{1}{2n}\|y - X\theta\|_2^2$ over
the ball $\|\theta\|_1 \le \|\theta^*\|_1$ satisfies

$$\|\hat\theta - \theta^*\|_2 \le \frac{4}{\kappa} \sqrt{s}\, \Big\|\frac{X^\top w}{n}\Big\|_\infty.$$

The first source assumes the condition over $\mathcal{C}(S; 3)$, which implies the one over
$\mathcal{C}(S; 1)$; its proof only uses the latter.

## Sources

- T. Hastie, R. Tibshirani and M. J. Wainwright, *Statistical Learning with Sparsity: The Lasso and Generalizations*, CRC Press, 2015: <https://hastie.su.domains/StatLearnSparsity/>, Theorem 11.1(a).
- M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University Press, 2019, §7.3.2 (bounds on $\ell_2$-error for hard sparse models).
