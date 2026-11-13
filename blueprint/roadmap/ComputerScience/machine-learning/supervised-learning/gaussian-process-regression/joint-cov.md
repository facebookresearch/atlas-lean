# Joint prior covariance in Gaussian-process regression

The joint prior covariance of the test values `f(x*)` and the noisy training targets
`y = f(x) + ε`, `ε ~ N(0, σ² I)`: `[[K(x*, x*), K(x*, x)], [K(x, x*), K(x, x) + σ² I]]`.
