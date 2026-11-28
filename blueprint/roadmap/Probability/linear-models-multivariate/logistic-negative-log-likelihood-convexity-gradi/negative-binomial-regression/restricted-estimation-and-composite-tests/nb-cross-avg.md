# Averaged cross term of a negative binomial sample

For covariate rows $x_i$, offsets $o_i$, counts $y_i$, a null coefficient $\beta_0$ and a shape $\theta$, the averaged cross term is $n^{-1}\sum_{i<n}\frac{(y_i - \mu_i)\mu_i}{(\theta + \mu_i)^2}x_i$ with $\mu_i = e^{x_i^\top\beta_0 + o_i}$: the $\theta$-derivative of the averaged coefficient score. For $n = 0$ the average is $0$ ($0^{-1} = 0$).
