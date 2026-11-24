# Shape derivative of the coefficient score

For covariate rows $x_i$, offsets $o_i$ and counts $y_i$ of a sample, a null coefficient $\beta_0$ and a shape $\theta$, let $S_n(\theta) = \sum_{i<n}\frac{\theta(y_i - \mu_i)}{\theta + \mu_i}x_i$ with $\mu_i = e^{x_i^\top\beta_0 + o_i}$ be the coefficient score and $C_n(\theta) = n^{-1}\sum_{i<n}\frac{(y_i - \mu_i)\mu_i}{(\theta + \mu_i)^2}x_i$ the averaged cross term. For $\theta > 0$, $\theta \mapsto S_n(\theta)$ is differentiable with derivative $nC_n(\theta)$.
