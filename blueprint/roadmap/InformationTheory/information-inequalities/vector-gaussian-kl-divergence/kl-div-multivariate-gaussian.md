# Kullback-Leibler divergence between multivariate Gaussians

Let $\iota$ be a nonempty finite index set with $n = \lvert \iota \rvert \ge 1$, and write $\mathcal{N}(m, S)$ for the Gaussian measure on the Euclidean space $\mathbb{R}^{\iota}$ with mean $m$ and covariance matrix $S$.

Let $m, q \in \mathbb{R}^{\iota}$ and let $S, T$ be positive definite real $\iota \times \iota$ matrices. Then the Kullback-Leibler divergence, in nats, is

$$\mathrm{KL}\big(\mathcal{N}(m, S) \,\|\, \mathcal{N}(q, T)\big) = \frac{1}{2}\left(\log\frac{\det T}{\det S} - n + \operatorname{tr}(T^{-1} S) + (m - q)^{\top} T^{-1} (m - q)\right)$$

with the right side read in $[0,\infty]$ (a real number $t$ is read as $\max(t,0)$).
