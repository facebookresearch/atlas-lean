# Integrals under the negative binomial regression law

Consider negative binomial regression with joint parameter $p = (\beta, \theta)$, coefficients $\beta$ and shape $\theta$: an observation $z = (x, y)$ (covariate row $x$, count $y$) has density $f_p(z) = \mathrm{NB}(y; \theta, e^{x^\top\beta})$, with closed-form score $s_p(z)$ and observed information $J_p(z)$. For an s-finite covariate law $\mu_X$, $\theta_0 > 0$ and $g$ integrable under the law $f_{p_0}\,(\mu_X \otimes \text{count})$, $\int g = \int\sum_k\mathrm{NB}(k; \theta_0, e^{x^\top\beta_0})\,g(x, k)\,d\mu_X(x)$.
