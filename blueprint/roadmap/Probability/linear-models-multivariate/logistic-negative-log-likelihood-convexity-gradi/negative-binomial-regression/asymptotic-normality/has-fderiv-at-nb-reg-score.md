# Derivative of the closed-form negative binomial score

Consider negative binomial regression with joint parameter $p = (\beta, \theta)$, coefficients $\beta$ and shape $\theta$: an observation $z = (x, y)$ (covariate row $x$, count $y$) has density $f_p(z) = \mathrm{NB}(y; \theta, e^{x^\top\beta})$, with closed-form score $s_p(z)$ and observed information $J_p(z)$. At every $p$ with $\theta > 0$, the derivative of $p \mapsto s_p(z)$ is $-J_p(z)$.
