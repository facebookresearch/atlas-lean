# Shape score of a negative binomial count

For a shape $\theta$, a count $y$ and a linear predictor $\eta$, the score with respect to the shape is $\sum_{j<y}\frac1{\theta + j} + \log\theta + 1 - \log(\theta + \mu) - \frac{y + \theta}{\theta + \mu}$ with $\mu = e^\eta$. For any real $\theta$; real division and inversion use $x/0 = 0$ and $0^{-1} = 0$. Here $\log$ is the real logarithm extended by $\log 0 = 0$ and $\log x = \log|x|$ for $x < 0$.
