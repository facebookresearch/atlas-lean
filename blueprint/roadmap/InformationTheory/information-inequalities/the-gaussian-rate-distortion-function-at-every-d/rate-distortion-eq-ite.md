# Gaussian rate-distortion function

Let $\sigma^2 > 0$ and $D \ge 0$. Assume the matching bounds hold strictly inside the range: for every $d$ with $0 < d < \sigma^2$,

$$\frac{\ln(\sigma^2 / d)}{2 \ln 2} \le R(d) \le \frac{\ln(\sigma^2 / d)}{2 \ln 2}.$$

Then

$$R(D) = \begin{cases} \infty & \text{if } D = 0, \\ \dfrac{\ln(\sigma^2 / D)}{2 \ln 2} & \text{if } 0 < D < \sigma^2, \\ 0 & \text{if } D \ge \sigma^2, \end{cases}$$

the endpoint cases holding without the assumed bounds. Here $R(D) \in [0, \infty]$ is the Gaussian rate-distortion function in bits: the infimum of the mutual information $I(\mu)$ over all probability measures $\mu$ on $\mathbb{R}^2$ with first marginal $\mathcal{N}(0, \sigma^2)$ and $\int (x - y)^2 \, d\mu \le D$ (the infimum over the empty set, for $D < 0$, being $\infty$).
