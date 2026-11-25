# Likelihood ratio of Gaussians with a common covariance

Let $\iota$ be a finite index set, $s_0, s_1 \in \mathbb{R}^\iota$ and $R \in \mathbb{R}^{\iota \times \iota}$ positive definite. Define the log-likelihood ratio statistic

$$\Lambda(y) = (s_1 - s_0)^{\mathsf T} R^{-1} y - \tfrac12\left(s_1^{\mathsf T} R^{-1} s_1 - s_0^{\mathsf T} R^{-1} s_0\right).$$

Then the Radon–Nikodym derivative of $\mathcal N(s_1, R)$ with respect to $\mathcal N(s_0, R)$ satisfies

$$\frac{d\,\mathcal N(s_1, R)}{d\,\mathcal N(s_0, R)}(y) = e^{\Lambda(y)}$$

for Lebesgue-almost every $y \in \mathbb{R}^\iota$.
