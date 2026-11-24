# Components of the negative binomial score vector

For a shape $\theta$, design $X$, offset $o$, responses $y$ and coefficients $\beta$, component $j$ of the score vector is $\sum_iX_{ij}s_i$ with $s_i = \theta(y_i - \mu_i)/(\theta + \mu_i)$ and $\mu_i = e^{(X\beta)_i + o_i}$.
