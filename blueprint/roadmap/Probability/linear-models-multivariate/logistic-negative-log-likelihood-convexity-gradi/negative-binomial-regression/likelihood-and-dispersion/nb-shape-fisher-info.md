# Fisher shape information of a negative binomial count

For a shape $\theta$ and a linear predictor $\eta$, the expected shape information is $\mathbb{E}\big[\sum_{j<Y}(\theta + j)^{-2}\big] - \frac1\theta + \frac1{\theta + \mu}$ for $Y \sim \mathrm{NB}(\theta, \mu)$, with $\mu = e^\eta$. Inverses of zero are read as $0^{-1} = 0$. The expectation is the series $\sum_k(\cdot)\,\mathrm{NB}(\theta, \mu)\{k\}$, taken as $0$ if it is not summable.
