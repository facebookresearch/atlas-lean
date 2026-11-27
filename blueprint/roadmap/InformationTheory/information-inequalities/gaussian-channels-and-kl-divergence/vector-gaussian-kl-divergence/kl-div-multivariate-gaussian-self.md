# Kl Div multivariate Gaussian self

Let $\iota$ be a finite index set with $n = \lvert \iota \rvert$, and write $\mathcal{N}(m, S)$ for the Gaussian measure on the Euclidean space $\mathbb{R}^{\iota}$ with mean $m$ and covariance matrix $S$.

Let $m \in \mathbb{R}^{\iota}$ and let $S$ be a positive definite real $\iota \times \iota$ matrix. Then the Kullback-Leibler divergence of $\mathcal{N}(m, S)$ from itself equals the closed form at equal parameters, which evaluates to zero:

$$\mathrm{KL}\big(\mathcal{N}(m, S) \,\|\, \mathcal{N}(m, S)\big) = \frac{1}{2}\left(\log\frac{\det S}{\det S} - n + \operatorname{tr}(S^{-1} S) + (m - m)^{\top} S^{-1} (m - m)\right) = 0.$$
