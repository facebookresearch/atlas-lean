# Posterior kernel of ridge regression

For $s \ge 0$ let $\varphi_s$ be the density of
$N(0, s)$, $\varphi_s(x) = (2 \pi s)^{-1/2} e^{-x^2 / (2 s)}$, with $\varphi_0$ the zero function.
For a real design matrix $X$ with $m$ rows and columns indexed by a finite type $\iota$, responses
$y \in \mathbb{R}^m$, variances $v, \tau \ge 0$ and $\theta \in \mathbb{R}^\iota$, the posterior
kernel is the Gaussian likelihood of $y$ times the prior density of $\theta$:

$$p(\theta) = \prod_{k=1}^{m} \varphi_v(y_k - (X\theta)_k) \prod_{i} \varphi_\tau(\theta_i).$$

This is the posterior kernel of linear regression with Gaussian noise of variance $v$ and
independent $N(0, \tau)$ priors on the coordinates of $\theta$; it is meaningful for
$v, \tau > 0$.
