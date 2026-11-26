# Lasso p-value of the critical regularization strength

**Setting.** For a target gene with centered expression $y\in\mathbb{R}^n$ over $n$ samples and $k$ centered candidate regulators $X = (x_1,\dots,x_k)\in\mathbb{R}^{n\times k}$, the lasso path is

$$\hat\beta(\lambda) = \arg\min_{\beta\in\mathbb{R}^k}\frac{1}{2n}\lVert y - X\beta\rVert_2^2 + \lambda\lVert\beta\rVert_1, \qquad \lambda\ge0.$$

Let $\sigma_i^2 = \lVert x_i\rVert_2^2/n$, let $r(\lambda) = y - X\hat\beta(\lambda)$ be the residual with variance $\sigma_r^2(\lambda) = \lVert r(\lambda)\rVert_2^2/n$, and let the **critical regularization strength** of regulator $i$ be $\lambda_i = \sup\{\lambda : \hat\beta_i(\lambda)\neq0\}$, the point on the path where $x_i$ first enters the model.

**Activity criterion (Proposition 1).** For every $\lambda>0$,

$$\hat\beta_i(\lambda)\neq0 \iff \lambda < \sigma_i\,\sigma_r(\lambda)\,\bigl|\operatorname{cor}(x_i, r(\lambda))\bigr|.$$

**Null distributions.** If $x_i$ has i.i.d. standard normal entries, then for any fixed $v$, $n\sigma_{x_i}^2\operatorname{cor}^2(x_i,v)\sim\chi^2(1)$ (Proposition 2). Two nulls for a non-regulator are used: the *normal* null, $x_{ji}$ i.i.d. $\mathcal{N}(0,\sigma_i^2)$, and the *spherical* null, $x_i$ uniform on the sphere of radius $\sigma_i\sqrt n$.

**Lasso p-value.** For the observed critical strength $\tilde\lambda_i$, approximating $P(\lambda_i\ge\tilde\lambda_i)$ by $P(\hat\beta_i(\tilde\lambda_i)\neq0)$ gives, with $u_i = \tilde\lambda_i/(\sigma_i\sigma_r(\tilde\lambda_i))$,

$$p_i^{\rm normal} = 1 - F_{\chi^2(1)}\bigl(n\,u_i^2\bigr), \qquad p_i^{\rm spherical} = 2 - 2F_{t(n-2)}\!\left(u_i\sqrt{\frac{n-2}{1-u_i^2}}\right).$$

For the first predictor to enter, the spherical p-value equals the Pearson-correlation p-value of $x_i$ and $y$, and the two nulls agree as $n\to\infty$.

## Expansion

Proposition 1 is the one-dimensional subgradient condition: holding the other coefficients at their lasso values, $\hat\beta_i>0$ iff the right derivative of the objective in $\beta_i$ at $0^+$ is negative, i.e. $\frac1n x_i^\top(-r(\lambda)) + \lambda<0$, and $\frac1n x_i^\top r = \sigma_i\sigma_r\operatorname{cor}(x_i,r)$; the negative case is symmetric. Proposition 2 follows from rotation invariance of the Gaussian: choosing $v$ with two nonzero entries $\pm\sqrt{n/2}$ reduces the statistic to $((x_1-x_2)/\sqrt2)^2$. Under the spherical null, $|\operatorname{cor}|$ has the law of the sample correlation with an independent vector, whose $t$-transform is $t(n-2)$. The approximation drops the probability that $x_i$ is active somewhere above $\tilde\lambda_i$ but inactive at $\tilde\lambda_i$ (predictors can leave and re-enter the path), so it under-estimates p-values slightly, least for the strongest regulators that enter early.

## Sources

- L. Wang and T. Michoel, *Controlling false discoveries in Bayesian gene networks with lasso regression p-values*, arXiv:1701.07011 (2017), Methods ("Lasso p-value") and Supplementary Sections S1–S2 (Propositions 1–2, normal and spherical null p-values). <https://doi.org/10.48550/arXiv.1701.07011>
