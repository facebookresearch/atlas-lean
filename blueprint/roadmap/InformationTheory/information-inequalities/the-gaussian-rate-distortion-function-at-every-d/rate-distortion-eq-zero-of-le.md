# Rate Distortion eq zero of le

Let $\sigma^2 \ge 0$ and $D \ge \sigma^2$. Then

$$R(D) = 0,$$

since the constant reconstruction $\hat{X} = 0$, independent of the source, is feasible at level $D$ and carries no information. Here $R(D) \in [0, \infty]$ is the Gaussian rate-distortion function in bits: the infimum of the mutual information $I(\mu)$ over all probability measures $\mu$ on $\mathbb{R}^2$ with first marginal $\mathcal{N}(0, \sigma^2)$ and $\int (x - y)^2 \, d\mu \le D$ (the infimum over the empty set, for $D < 0$, being $\infty$).
