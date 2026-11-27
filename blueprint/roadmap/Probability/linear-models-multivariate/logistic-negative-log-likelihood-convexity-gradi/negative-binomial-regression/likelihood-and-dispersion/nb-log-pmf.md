# Negative binomial log mass function in shape and linear predictor

For a shape $\theta$, a count $y$ and a linear predictor $\eta$ (mean $\mu = e^\eta$), the negative binomial log mass function is $\sum_{j<y}\log(\theta + j) - \log y! + \theta\log\theta + y\eta - (y + \theta)\log(\theta + e^\eta)$; for $\theta > 0$ it is $\log\mathrm{NB}(y; \theta, e^\eta)$. Here $\log$ is the real logarithm extended by $\log 0 = 0$ and $\log x = \log|x|$ for $x < 0$.
