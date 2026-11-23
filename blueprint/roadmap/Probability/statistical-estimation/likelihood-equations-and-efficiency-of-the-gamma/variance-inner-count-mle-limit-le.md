# No projection of the MLE limit is more variable than the moment limit

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
the expectation. Let $Y_1$ be a random vector in $\mathbb{R}^2$ on $(\Omega_1, P_1)$ with
$\langle Y_1, t \rangle \sim N(0, E \langle \psi, t \rangle^2)$, the Gaussian vector of the
[limit theorem for score roots](tendsto-in-distribution-count-mle.md), and $Y_2$ one on
$(\Omega_2, P_2)$ with $\langle Y_2, t \rangle \sim N(0, E \langle g, t \rangle^2)$, that of the
[moment limit theorem](tendsto-in-distribution-mom.md), for every $t \in \mathbb{R}^2$. Then for
every direction $u \in \mathbb{R}^2$

$$\mathrm{Var}\, \langle I^{-1} Y_1, u \rangle \le \mathrm{Var}\, \langle -J^{-1} Y_2, u \rangle:$$

consistent roots of the score equations are asymptotically at least as efficient as the
method-of-moments estimator.
