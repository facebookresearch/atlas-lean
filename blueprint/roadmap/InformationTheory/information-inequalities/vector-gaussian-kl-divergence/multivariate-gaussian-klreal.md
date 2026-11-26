# Multivariate Gaussian KLReal

Let $\iota$ be a finite index set with $n = \lvert \iota \rvert$. For vectors $m, q \in \mathbb{R}^{\iota}$ and real $\iota \times \iota$ matrices $S, T$, the closed form of the Gaussian Kullback-Leibler divergence, in nats, is

$$\frac{1}{2}\left(\log\frac{\det T}{\det S} - n + \operatorname{tr}(T^{-1} S) + (m - q)^{\top} T^{-1} (m - q)\right)$$

It is defined for all $m, q, S, T$, with the conventions $x / 0 = 0$, $\log 0 = 0$, $\log x = \log \lvert x \rvert$ for $x < 0$, and $T^{-1} = 0$ when $T$ is singular.
