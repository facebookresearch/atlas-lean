# Integral output Quadratic eq trace

Let $\iota$ and $\kappa$ be finite index sets, let $H \in \mathbb{R}^{\iota \times \kappa}$ and $A \in \mathbb{R}^{\iota \times \iota}$ be real matrices, and let $\rho$ be a probability measure on the Euclidean space $\mathbb{R}^\kappa$ with finite second moment. Suppose $m = \int x \, d\rho(x)$ is the mean of $\rho$ and $K \in \mathbb{R}^{\kappa \times \kappa}$ is its covariance matrix, $K_{ab} = \operatorname{Cov}_\rho(x_a, x_b)$ for all $a, b$. Then the expected centered output quadratic form is a trace:

$$\int (Hx - Hm)^\top A \,(Hx - Hm) \, d\rho(x) = \operatorname{tr}\!\left(A H K H^\top\right).$$
