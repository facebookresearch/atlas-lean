# Capacity of the Gaussian MIMO channel by water-filling

This node covers the capacity of a fixed linear Gaussian vector channel. Let $H$ be a real $r \times t$ matrix, $R$ a positive-definite
$r \times r$ noise covariance and $P > 0$, and consider $Y = HX + Z$ with $Z \sim N(0, R)$ independent of $X$ and the power constraint
$\mathbb{E}\|X\|^2 \le P$. Then the supremum of the mutual information $I(X; Y)$ over input laws satisfying the constraint equals

$$C = \max_{K \succeq 0,\ \operatorname{tr}K \le P}\ \tfrac12\log\det\big(I + R^{-1}HKH^{\mathsf T}\big) = \sum_i \tfrac12\log^+(\mu\,\sigma_i),$$

where, for $H \ne 0$, $\sigma_i$ are the positive eigenvalues of $H^{\mathsf T}R^{-1}H$ and the water level $\mu > 0$ is the unique solution of
$\sum_i (\mu - 1/\sigma_i)^+ = P$; for $H = 0$ the output is independent of the input and $C = 0$. For $H \ne 0$ the supremum is attained by a centred Gaussian input whose covariance is diagonal in the eigenbasis of
$H^{\mathsf T}R^{-1}H$ with entries $(\mu - 1/\sigma_i)^+$.

## Expansion

A good expansion proves that Gaussian inputs maximize mutual information for a given input covariance, reduces the covariance
optimization to parallel channels by whitening and a singular value decomposition, and solves it by water-filling with its KKT certificate.
Operational coding theorems and fading channels are separate nodes.

## Sources

- E. Telatar, Capacity of multi-antenna Gaussian channels, *European Transactions on Telecommunications* 10 (1999) 585-595.
- T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd edition, Wiley, 2006, for parallel Gaussian channels.
