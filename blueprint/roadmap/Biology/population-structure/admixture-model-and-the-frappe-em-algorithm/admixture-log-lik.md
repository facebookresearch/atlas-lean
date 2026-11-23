# Admixture log-likelihood

Let $I$ and $J$ be finite and $g$ a genotype matrix with entries in $\{0, 1, 2\}$. For [admixture parameters](params.md) $\theta$, the admixture log-likelihood is

$$\ell_g(\theta) = \sum_{i \in I} \sum_{j \in J} \Bigl(g_{ij} \log \phi_{ij}(\theta) + (2 - g_{ij}) \log\bigl(1 - \phi_{ij}(\theta)\bigr)\Bigr),$$

where $\phi_{ij}$ is the [reference-allele probability](qf.md).
