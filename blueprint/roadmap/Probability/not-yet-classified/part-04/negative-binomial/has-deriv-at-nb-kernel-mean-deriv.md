# Has Deriv At nb Kernel Mean deriv

The mean-scale second derivative: for `θ > 0` and `μ > 0`, the derivative of
`θ (y - μ) / (μ (θ + μ))` is `-y / μ² + (y + θ) / (θ + μ)²`. Unlike the log-link second derivative
`-nbObsWeight θ y η` it is not sign-definite: it is positive at `y = 0`.
