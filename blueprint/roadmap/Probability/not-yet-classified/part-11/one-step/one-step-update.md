# One-step Newton update

In a finite-dimensional real inner product space, for a linear map $J$, an initial estimate $\theta_{\text{init}}$, a total score $S_n$ and sample size $n$, the one-step update is

$$\theta_{\text{init}} + J^{-1}\Bigl(\frac{S_n}{n}\Bigr),$$

with $S_n/n = 0$ when $n = 0$, by the convention $a/0 = 0$, where $J^{-1}$ is the inverse of $J$ when $J$ is invertible and $0$ otherwise.
