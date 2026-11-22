# Bayes' theorem for a linear-Gaussian observation, precision form

Let $n$ and $p$ be finite index sets, and let $x$ and $v$ be independent measurable random vectors
in $\mathbb{R}^n$ and $\mathbb{R}^p$ on a probability space. Suppose the prior is
$x \sim N(m, \Lambda^{-1})$ with a positive definite precision matrix $\Lambda$, and the noise is
$v \sim N(0, \sigma^2 I)$ with $\sigma^2 > 0$. Let $X$ be any real $p \times n$ design matrix (of
any rank) and $y = X x + v$. Then for almost every $y$ with respect to the law of $X x + v$, the
conditional distribution of $x$ given $X x + v = y$ is the Gaussian law with covariance $\Pi^{-1}$
and mean $\Pi^{-1}(\Lambda m + \sigma^{-2} X^\top y)$, where

$$\Pi = \Lambda + \sigma^{-2} X^\top X$$

is the (positive definite) posterior precision. This is the [gain form](cond-distrib-linear-add-of-indep-fun.md)
rewritten by the push-through identity.
