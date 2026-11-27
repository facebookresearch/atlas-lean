# GREML covariance matrix $\sigma_g^2 K + \sigma_e^2 I$

For a real square matrix $K$ indexed by a finite set and a parameter
$\theta = (\sigma_g^2, \sigma_e^2) \in \mathbb{R}^2$, the GREML covariance is

$$V(\theta) = \sigma_g^2 K + \sigma_e^2 I.$$

It is defined for every real $K$ and $\theta$. It is the phenotypic covariance of the GREML model
$y \sim N(X\beta, \sigma_g^2 K + \sigma_e^2 I)$ when it is positive semidefinite, for example when
$K$ is symmetric positive semidefinite, as the
[genetic relationship matrix](pos-semidef-grm.md) is, and $\sigma_g^2, \sigma_e^2 \ge 0$.
