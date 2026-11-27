# Averaged joint negative binomial log-likelihood

For covariate rows $x_i$, offsets $o_i$ and counts $y_i$ of a sample and $p = (\beta, \theta)$, the averaged joint log-likelihood of the first $n$ observations is $n^{-1}\sum_{i<n}\log\mathrm{NB}(y_i; \theta, e^{x_i^\top\beta + o_i})$ (in the form valid for all real $\theta$). For $n = 0$ the average is $0$ ($0^{-1} = 0$). Here $\log$ is the real logarithm extended by $\log 0 = 0$ and $\log x = \log|x|$ for $x < 0$.
