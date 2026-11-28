# Composite likelihood-ratio statistic for negative binomial coefficients

For observations $z_0, \dots, z_{n-1}$, a joint estimate $\hat p$, a null coefficient $\beta_0$ and a restricted shape estimate $\tilde\theta$, the composite likelihood-ratio statistic is $2\sum_{i<n}\big(\log f_{\hat p}(z_i) - \log f_{(\beta_0, \tilde\theta)}(z_i)\big)$, with $f$ the negative binomial regression density. Here $\log$ is the real logarithm extended by $\log 0 = 0$ and $\log x = \log|x|$ for $x < 0$. A zero density value therefore contributes $\log 0 = 0$.
