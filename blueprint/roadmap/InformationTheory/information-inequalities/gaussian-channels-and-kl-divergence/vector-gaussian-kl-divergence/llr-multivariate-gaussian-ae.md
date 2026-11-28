# Llr multivariate Gaussian ae

Let $\iota$ be a finite index set with $n = \lvert \iota \rvert$, and write $\mathcal{N}(m, S)$ for the Gaussian measure on the Euclidean space $\mathbb{R}^{\iota}$ with mean $m$ and covariance matrix $S$.

Let $m, q \in \mathbb{R}^{\iota}$ and let $S, T$ be positive definite real $\iota \times \iota$ matrices. Then for $\mathcal{N}(m, S)$-almost every $x$, the log-likelihood ratio $\log \frac{d\mathcal{N}(m, S)}{d\mathcal{N}(q, T)}(x)$ equals

$$\frac{1}{2}\left(\log\frac{\det T}{\det S} - (x - m)^{\top} S^{-1} (x - m) + (x - q)^{\top} T^{-1} (x - q)\right)$$
