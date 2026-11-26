# $\ell_2$-error bound for the Lagrangian Lasso

Let $y = X\theta^* + w$ with $\theta^*$ vanishing off a set $S$ of $s$ coordinates. Suppose that
$X$ satisfies the restricted eigenvalue condition with constant $\kappa$ over
$\mathcal{C}(S; 3)$, and let $\lambda > 0$ with $\lambda \ge 2\|X^\top w / n\|_\infty$. Then
every minimiser $\hat\theta$ of the Lagrangian Lasso objective satisfies

$$\|\hat\theta - \theta^*\|_2 \le \frac{3}{\kappa} \sqrt{s}\, \lambda.$$

With Gaussian noise of variance $\sigma^2$ and normalized columns, the choice
$\lambda \asymp \sigma\sqrt{\log d / n}$ gives the rate $\sigma\sqrt{s \log d / n}$, which is
minimax optimal up to the logarithmic factor (Hastie et al. 2015, Example 11.1; Raskutti,
Wainwright and Yu 2011).

## Sources

- T. Hastie, R. Tibshirani and M. J. Wainwright, *Statistical Learning with Sparsity: The Lasso and Generalizations*, CRC Press, 2015: <https://hastie.su.domains/StatLearnSparsity/>, Theorem 11.1(b) and Example 11.1.
- G. Raskutti, M. J. Wainwright and B. Yu, *Minimax rates of estimation for high-dimensional linear regression over $\ell_q$-balls*, IEEE Trans. Inform. Theory 57 (2011), 6976–6994, arXiv:0910.2042.
- M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University Press, 2019, §7.3.2 (bounds on $\ell_2$-error for hard sparse models).
- P. J. Bickel, Y. Ritov and A. B. Tsybakov, *Simultaneous analysis of Lasso and Dantzig selector*, Ann. Statist. 37 (2009), 1705–1732.

## Background

- [Hoeffding's inequality](../../concentration-inequalities/hoeffding-s-inequality/README.md): the choice of $\lambda$ above $2\|X^\top w/n\|_\infty$ with high probability is a sub-Gaussian maximal inequality.
