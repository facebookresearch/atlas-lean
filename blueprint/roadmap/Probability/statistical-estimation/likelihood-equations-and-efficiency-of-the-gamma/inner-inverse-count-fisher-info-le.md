# Efficiency of the count MLE relative to the moment estimator

Let $\mu_X$ be a probability measure on $\mathbb{N}$, the law of a count $K$, and write $E$ for
expectations under $\mu_X$. Let $\sigma, a, b > 0$, let $E K^4 < \infty$, and assume the
profile-information condition $\tau_0 > \sigma / (a (b + \sigma))$ for $\tau_0 = E[\varphi_K(a)]$,
the expected [trigamma increment](trigamma-increment.md), so that the
[Fisher information matrix](count-fisher-info.md) $I = I(a, b, \sigma, \tau_0)$ is invertible. Write
$\psi = \psi_\sigma((a, b), K)$ for the [score of one count](count-score.md),
$g = g_\sigma((a, b), K)$ for the [moment estimating function](mom-est-fun.md) and
$J = J(a, b, \sigma)$ for the invertible [moment Jacobian](mom-jacobian.md). Assume the information
identity $\langle I z, z \rangle = E \langle \psi, z \rangle^2$ for every $z \in \mathbb{R}^2$ (the
second Bartlett identity) and the differentiated unbiasedness of the moment equations,
$\langle J x, w \rangle = -E\bigl[\langle \psi, x \rangle \langle g, w \rangle\bigr]$ for all
$x, w \in \mathbb{R}^2$, which is $\partial_\theta E_\theta[g(\theta, K)] = 0$ differentiated under
the expectation. Then for every direction $u \in \mathbb{R}^2$

$$\langle I^{-1} u, u \rangle \le E \bigl\langle g, (J^{-1})^{\mathsf T} u \bigr\rangle^2.$$

The left side is the variance of $\langle Z, u \rangle$ for the limit $Z \sim N(0, I^{-1})$ of
consistent score roots, the right side that of the limit $-J^{-1} N(0, E[g g^{\mathsf T}])$ of the
moment estimator ([variances](variance-inner-count-mle-limit-le.md)): the asymptotic covariance of
the moment estimator dominates the inverse Fisher information in the Loewner order (Godambe 1960;
the efficiency of this moment estimator was studied by Fisher 1941 and Anscombe 1950).
