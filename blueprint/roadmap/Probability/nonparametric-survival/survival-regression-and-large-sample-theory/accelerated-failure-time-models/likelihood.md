# Censored log-linear likelihood

The censored log-linear accelerated failure time likelihood is $\prod_i(f_0(z_i)/\sigma)^{\delta_i}S_0(z_i)^{1-\delta_i}$ with $z_i = (y_i - \langle\beta, x_i\rangle)/\sigma$. As for [the contribution of one observation](lik-contrib.md), division by zero gives $0$.
