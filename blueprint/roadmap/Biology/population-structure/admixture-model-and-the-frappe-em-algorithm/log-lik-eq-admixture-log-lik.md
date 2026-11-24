# The EM log-likelihood of the allele copies is the admixture log-likelihood

Let $I$ and $J$ be finite and $g$ a genotype matrix with entries in $\{0, 1, 2\}$. For all [admixture parameters](params.md) $\theta$,

$$\sum_{n=0}^{N-1} \log \sum_{k \in K} p_\theta(x_n, k) = \ell_g(\theta),$$

where $x_0, \dots, x_{N-1}$ is the [allele-copy data](data.md), $p_\theta$ the [joint weight](joint.md) and $\ell_g$ the [admixture log-likelihood](admixture-log-lik.md).
