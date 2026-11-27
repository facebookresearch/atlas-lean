# Variance components of the linear mixed model

Variance components on $n$ individuals are a triple $(K, \sigma_g^2, \sigma_e^2)$ consisting of a positive semidefinite real $n \times n$ matrix $K$ (the genetic relationship matrix), a real number $\sigma_g^2 \ge 0$ (the genetic variance) and a real number $\sigma_e^2 > 0$ (the environmental variance).

They parametrize the linear mixed model $y = X\beta + g + e$ with $g \sim N(0, \sigma_g^2 K)$ and $e \sim N(0, \sigma_e^2 \mathrm{I})$.
