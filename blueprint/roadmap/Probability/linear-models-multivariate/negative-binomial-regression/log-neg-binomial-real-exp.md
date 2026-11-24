# The negative binomial kernel is the log mass function up to a constant

For $\theta > 0$, a linear predictor $\eta$ and a count $k$, the negative binomial law with shape $\theta$ and mean $e^\eta$ satisfies

$$\log P(Y = k) = \log\frac{\theta^{(k)}}{k!} + \theta\log\theta + k\eta - (k + \theta)\log(\theta + e^\eta),$$

where $\theta^{(k)} = \theta(\theta + 1)\cdots(\theta + k - 1)$.
