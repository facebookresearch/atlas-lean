# Censored log-linear log-likelihood

The censored log-linear log-likelihood is $\ell(\beta, \sigma) = \sum_i\delta_i(\log f_0(z_i) - \log\sigma) + (1 - \delta_i)\log S_0(z_i)$ with $z_i = (y_i - \langle\beta, x_i\rangle)/\sigma$. As for [the contribution of one observation](log-lik-contrib.md), $\log$ is the real logarithm extended by $\log 0 = 0$ and $\log x = \log|x|$ for $x < 0$, and division by zero gives $0$.
