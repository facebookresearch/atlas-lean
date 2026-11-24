# Observed information of the negative binomial regression model

Consider negative binomial regression with joint parameter $p = (\beta, \theta)$, coefficients $\beta$ and shape $\theta$: an observation $z = (x, y)$ (covariate row $x$, count $y$) has density $f_p(z) = \mathrm{NB}(y; \theta, e^{x^\top\beta})$, with closed-form score $s_p(z)$ and observed information $J_p(z)$. At every $p$ with $\theta > 0$, the observed information $-n^{-1}\sum_{i<n}\nabla_p^2\log f_p(z_i)$ equals $n^{-1}\sum_{i<n}J_p(z_i)$.
