# Negative binomial regression score vector

For a shape $\theta$, design $X$, offset $o$, responses $y$ and coefficients $\beta$, the score vector is $X^\top s$ with $s_i = \theta(y_i - \mu_i)/(\theta + \mu_i)$ and $\mu_i = e^{(X\beta)_i + o_i}$.
