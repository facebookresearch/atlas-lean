# The admixture log-likelihood is monotone along the iterates

Let $I$ and $J$ be finite, $K$ nonempty, and $g$ a genotype matrix with entries in $\{0, 1, 2\}$. Let $T$ be a map on [admixture parameters](params.md) with $\mathcal{Q}(\theta \mid \theta) \le \mathcal{Q}(T\theta \mid \theta)$ for every $\theta$, where $\mathcal{Q}$ is the EM objective of the [EM theorem](admixture-log-lik-le-of-em-q-le.md). Then for every $\theta_0$, the sequence $t \mapsto \ell_g(T^t \theta_0)$ is nondecreasing, where $\ell_g$ is the [admixture log-likelihood](admixture-log-lik.md).
