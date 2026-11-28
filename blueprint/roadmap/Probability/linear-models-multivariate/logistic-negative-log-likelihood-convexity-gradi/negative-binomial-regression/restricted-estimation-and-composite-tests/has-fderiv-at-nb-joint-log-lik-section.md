# Coefficient derivative of a shape section

For a design $X$, offset $o$ and counts $y$, let $\ell(\beta, \theta)$ be the joint negative binomial log-likelihood, $\ell_0(\theta) = \ell(\beta_0, \theta)$ its restriction to the null $\beta = \beta_0$, and $\ell_{\mathrm{prof}}(\theta) = \sup_\beta\ell(\beta, \theta)$ the profile log-likelihood of the shape. For $\theta > 0$, $b \mapsto \ell(b, \theta)$ is differentiable at $\beta$ with derivative $v \mapsto \langle v, X^\top s\rangle$, $s_i = \theta(y_i - \mu_i)/(\theta + \mu_i)$: the fixed-shape score.
