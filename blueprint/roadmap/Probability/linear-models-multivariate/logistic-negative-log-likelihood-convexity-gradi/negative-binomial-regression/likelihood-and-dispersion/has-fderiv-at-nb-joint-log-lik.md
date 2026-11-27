# Derivative of the joint negative binomial regression log-likelihood

For a design $X$, offset $o$ and counts $y$, let $\ell(\beta, \theta) = \sum_i\log\mathrm{NB}(y_i; \theta, e^{\eta_i})$ with $\eta = X\beta + o$ be the joint negative binomial log-likelihood. For $\theta > 0$, $\ell$ is differentiable at $(\beta, \theta)$ with derivative $(v, s) \mapsto \langle v, X^\top s(\beta, \theta)\rangle + s\sum_i\partial_\theta\log\mathrm{NB}(y_i; \theta, e^{\eta_i})$, where $s_i = \theta(y_i - \mu_i)/(\theta + \mu_i)$.
