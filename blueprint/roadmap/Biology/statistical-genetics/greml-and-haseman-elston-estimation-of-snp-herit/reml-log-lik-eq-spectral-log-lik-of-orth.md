# REML log-likelihood via an orthogonal rotation, at positive variances

Let $m$ and $r$ be finite index sets, $K$ a real $m \times m$ matrix, $A$ a real $r \times m$
matrix with $AA^\top = I$, and $Q$ a real $r \times r$ matrix with $QQ^\top = Q^\top Q = I$ such
that $QAK(QA)^\top = \operatorname{diag}(d)$. Let $\theta = (\sigma_g^2, \sigma_e^2)$ be a
parameter at which every [contrast variance](contrast-var.md)
$\lambda_i(\theta) = \sigma_g^2 d_i + \sigma_e^2$ is positive. Then for every $y \in \mathbb{R}^m$,
the restricted log-likelihood $\ell_A(\theta)$ of $y$ for $A$ at
$V(\theta) = \sigma_g^2 K + \sigma_e^2 I$, the logarithm of the density of the Gaussian law
$N(0, A V(\theta) A^\top)$ at $Ay$, is the [spectral criterion](spectral-log-lik.md) at the
rotated contrasts $w = QAy$:

$$\ell_A(\theta) = -\frac{|r|}{2} \log(2\pi) - \frac12 \sum_{i \in r} \log \lambda_i(\theta) -
\frac12 \sum_{i \in r} \frac{w_i^2}{\lambda_i(\theta)}.$$
