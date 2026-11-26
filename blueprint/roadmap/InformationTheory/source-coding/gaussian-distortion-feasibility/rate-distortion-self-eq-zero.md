# Rate Distortion self eq zero

Let $\sigma^2 \ge 0$. The Gaussian rate-distortion function at distortion level $D = \sigma^2$ vanishes:

$$R(\sigma^2) = 0,$$

since the constant reconstruction $\hat{X} = 0$ is feasible at level $\sigma^2$ and carries zero mutual information. Here $R(D)$ is the infimum of the mutual information, in bits, over all probability measures on $\mathbb{R}^2$ with first marginal $\mathcal{N}(0, \sigma^2)$ and $\int (x - y)^2 \, d\mu \le D$.
