# Coefficient score of a negative binomial sample

For covariate rows $x_i$, offsets $o_i$ and counts $y_i$, a null coefficient $\beta_0$ and a shape $\theta$, the coefficient score of the first $n$ observations is $\sum_{i<n}\frac{\theta(y_i - \mu_i)}{\theta + \mu_i}x_i$ with $\mu_i = e^{x_i^\top\beta_0 + o_i}$.
