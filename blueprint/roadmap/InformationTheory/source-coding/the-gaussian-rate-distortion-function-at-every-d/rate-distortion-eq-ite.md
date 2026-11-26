# Gaussian rate-distortion function

Let $\sigma^2 \ge 0$ and $D \in \mathbb{R}$. The feasible set $\mathcal{F}(\sigma^2, D)$ consists of the probability measures $\mu$ on $\mathbb{R}^2$ with $D \ge 0$, first marginal $\mathcal{N}(0, \sigma^2)$, and $\int (x - \hat x)^2 \, d\mu(x, \hat x) \le D$ (a lower integral in $[0, \infty]$). The mutual information of $\mu$ in bits is $I(\mu) = D_{\mathrm{KL}}(\mu \,\|\, \mu_1 \otimes \mu_2) / \log 2 \in [0, \infty]$, where $\mu_1, \mu_2$ are the marginals, and the rate-distortion function is $R(D) = \inf_{\mu \in \mathcal{F}(\sigma^2, D)} I(\mu) \in [0, \infty]$.

Let $\sigma^2 > 0$ and $D \ge 0$, and write $L(d) = \frac{\log(\sigma^2 / d)}{2 \log 2}$. Assume that $L(d) \le R(d)$ and $R(d) \le L(d)$ for every $d$ with $0 < d < \sigma^2$. Then

$$R(D) = \begin{cases} \infty & \text{if } D = 0, \\ L(D) & \text{if } 0 < D < \sigma^2, \\ 0 & \text{if } D \ge \sigma^2. \end{cases}$$

## Sources

T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed. (2006), Theorem 10.3.2.
