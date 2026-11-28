# The joint observed information is minus the Hessian

For a design $X$, offset $o$ and counts $y$, let $\ell(\beta, \theta) = \sum_i\log\mathrm{NB}(y_i; \theta, e^{\eta_i})$ with $\eta = X\beta + o$ be the joint negative binomial log-likelihood. For $\theta > 0$ and a direction $d = (u, s)$, the derivative at $t = 0$ of $t \mapsto \nabla\ell((\beta, \theta) + td)\cdot d$ is $-d^\top Jd$, with $J$ the joint observed information.
