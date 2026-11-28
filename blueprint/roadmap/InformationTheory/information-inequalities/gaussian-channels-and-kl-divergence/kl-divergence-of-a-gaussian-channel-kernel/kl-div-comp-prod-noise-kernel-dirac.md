# Kl Div comp Prod noise Kernel dirac

Let $\kappa$ and $\iota$ be finite index sets with $\iota$ nonempty, with input space $\mathbb{R}^{\kappa}$ and output space $\mathbb{R}^{\iota}$ of dimension $d = \lvert \iota \rvert$, both Euclidean, and let $H$ be a real $\iota \times \kappa$ matrix. Write $\mathcal{N}(m, S)$ for the Gaussian measure with mean $m$ and covariance matrix $S$.

Let $q \in \mathbb{R}^{\iota}$, let $R, T$ be positive definite real $\iota \times \iota$ matrices, and let $a \in \mathbb{R}^{\kappa}$. Let $k$ be the additive Gaussian noise kernel sending $x \in \mathbb{R}^{\kappa}$ to the law of $H x + Z$ with $Z \sim \mathcal{N}(0, R)$, that is, $k(x) = \mathcal{N}(H x, R)$. For the point-mass input $\delta_a$,

$$\mathrm{KL}\big(\delta_a \otimes k \,\|\, \delta_a \times \mathcal{N}(q, T)\big) = \frac{1}{2}\left(\log\frac{\det T}{\det R} - d + \operatorname{tr}(T^{-1} R) + (H a - q)^{\top} T^{-1} (H a - q)\right),$$

with the right side read in $[0,\infty]$ (a real number $t$ is read as $\max(t,0)$).
