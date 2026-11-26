# Rate Distortion antitone

Let $\sigma^2 \ge 0$. The Gaussian rate-distortion function is antitone in the distortion level: for all real $D \le D'$,

$$R(D') \le R(D).$$

Here $R(D) \in [0, \infty]$ is the Gaussian rate-distortion function in bits: the infimum of the mutual information $I(\mu)$ over all probability measures $\mu$ on $\mathbb{R}^2$ with first marginal $\mathcal{N}(0, \sigma^2)$ and $\int (x - y)^2 \, d\mu \le D$ (the infimum over the empty set, for $D < 0$, being $\infty$).
