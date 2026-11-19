# Gaussian likelihood of linear regression

Let $X$ be a real matrix with $m$ rows and
columns indexed by a finite set $\iota$, let $y \in \mathbb{R}^m$ and let $v \ge 0$. The Gaussian
likelihood with noise variance $v$ is the function of $\theta \in \mathbb{R}^\iota$ given by

$$
L(\theta) = \prod_{k=1}^{m} \frac{1}{\sqrt{2 \pi v}}
\exp\left(-\frac{(y_k - (X\theta)_k)^2}{2 v}\right).
$$

This is the likelihood of $y$ when $y_k = (X\theta)_k + \varepsilon_k$ with independent
$\varepsilon_k \sim N(0, v)$.

For $v = 0$ each factor is the zero function (with the convention $1/0 = 0$), not a Dirac kernel;
the results about this likelihood assume $v \neq 0$.
