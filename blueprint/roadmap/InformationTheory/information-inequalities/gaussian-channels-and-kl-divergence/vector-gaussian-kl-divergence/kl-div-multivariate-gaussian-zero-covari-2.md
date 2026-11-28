# Kl Div multivariate Gaussian zero covariance ne

Let $\iota$ be a nonempty finite index set with $n = \lvert \iota \rvert \ge 1$, and write $\mathcal{N}(m, S)$ for the Gaussian measure on the Euclidean space $\mathbb{R}^{\iota}$ with mean $m$ and covariance matrix $S$.

Let $m, q \in \mathbb{R}^{\iota}$ and let $T$ be a positive definite real $\iota \times \iota$ matrix. At the zero covariance the divergence is not the closed form:

$$\mathrm{KL}\big(\mathcal{N}(m, 0) \,\|\, \mathcal{N}(q, T)\big) \neq \max(G, 0), \qquad G = \frac{1}{2}\left(\log\frac{\det T}{\det 0} - n + \operatorname{tr}(T^{-1} 0) + (m - q)^{\top} T^{-1} (m - q)\right),$$

where $G$ uses $x / 0 = 0$ and $\log 0 = 0$, and $\max(G, 0)$ is its finite value in $[0, \infty)$; for example, for $n = 1$, $m = q = 0$ and $T = [1]$, $G = -\tfrac{1}{2}$ and $\max(G, 0) = 0$. The left side is $\infty$, so the positive-definiteness hypothesis on the first covariance in the closed-form formula cannot be dropped.
