# Scalar Gaussian divergence in vector form

Let $m, q \in \mathbb{R}$ and $s, t > 0$. The Kullback–Leibler divergence between real Gaussians equals the multivariate Gaussian closed form at dimension one, with means $(m)$, $(q)$ and covariances $[s]$, $[t]$:

$$D_{\mathrm{KL}}\big(\mathcal{N}(m, s) \parallel \mathcal{N}(q, t)\big) = \max\left\{\frac{1}{2}\left(\ln\frac{t}{s} - 1 + \frac{s}{t} + \frac{(m - q)^2}{t}\right),\ 0\right\},$$

in nats. The bracket is the closed form $\tfrac12\big(\ln\frac{\det T}{\det S} - n + \operatorname{tr}(T^{-1}S) + (m-q)^\top T^{-1}(m-q)\big)$ at $n = 1$, $S = [s]$, $T = [t]$.
