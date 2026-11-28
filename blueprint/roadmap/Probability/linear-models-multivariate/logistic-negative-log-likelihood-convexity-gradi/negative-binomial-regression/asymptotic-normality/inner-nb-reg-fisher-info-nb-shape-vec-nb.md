# The shape is orthogonal to the coefficients

Consider negative binomial regression with joint parameter $p = (\beta, \theta)$, coefficients $\beta$ and shape $\theta$: an observation $z = (x, y)$ (covariate row $x$, count $y$) has density $f_p(z) = \mathrm{NB}(y; \theta, e^{x^\top\beta})$, with closed-form score $s_p(z)$ and observed information $J_p(z)$. For an s-finite covariate law $\mu_X$ (reference measure $\mu_X \otimes$ counting measure), $\theta_0 > 0$, $J_{p_0}$ integrable with mean $I(p_0)$, the cross information vanishes: $\langle I(p_0)(0, 1), (t, 0)\rangle = 0$ for every $t$.
