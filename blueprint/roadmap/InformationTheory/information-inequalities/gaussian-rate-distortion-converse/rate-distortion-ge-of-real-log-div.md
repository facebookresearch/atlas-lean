# Gaussian rate-distortion converse

Let $0 < D < \sigma^2$. The Gaussian rate-distortion function at $D$, in bits, satisfies

$$R(D) \ge \frac{\ln(\sigma^2 / D)}{2 \ln 2} = \frac{1}{2} \log_2 \frac{\sigma^2}{D}.$$

Here $R(D) \in [0, \infty]$ is the infimum of the mutual information (in bits) over all probability measures $\mu$ on $\mathbb{R}^2$ whose first marginal is $\mathcal{N}(0, \sigma^2)$ and with $\int (x - y)^2 \, d\mu(x, y) \le D$.
