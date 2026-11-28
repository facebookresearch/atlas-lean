# Characteristic function of a weighted chi-square law

For a finite index set $k$ and weights $\lambda \in \mathbb{R}^k$, the characteristic function of $\sum_j \lambda_j \xi_j^2$, with $\xi_j$ **independent** standard normal variables, used in Davies' formula is

$$\varphi(t) = \prod_{j} (1 - 2 i \lambda_j t)^{-1/2}, \qquad t \in \mathbb{R},$$

where each power is the principal branch of the complex power; each base $1 - 2 i \lambda_j t$ has real part $1$.

Independence matters: for two identical copies $\xi_1 = \xi_2$ the characteristic function of $\lambda_1 \xi_1^2 + \lambda_2 \xi_2^2$ is $(1 - 2 i (\lambda_1 + \lambda_2) t)^{-1/2}$, not the product in general (the two agree when one weight is $0$).
