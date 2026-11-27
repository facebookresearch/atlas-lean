# Stationary law of the multi-allele diffusion with diploid selection

Steinrücken, Wang and Song (2013, Section 2.1) consider $K$ alleles with frequencies $x = (x_1, \dots, x_{K-1})$ and $x_K = 1 - |x|$ on the simplex $\Delta_{K-1}$, parent-independent mutation with scaled rates $\theta_i = 4Nu_i > 0$ and $|\theta| = \sum_{i=1}^K\theta_i$, and general diploid selection given by a symmetric matrix of scaled coefficients $\sigma_{ij} = 2Ns_{ij}$, where genotype $ij$ has fitness $1 + 2s_{ij}$ and $\sigma_{KK} = 0$. With marginal fitnesses $\sigma_i(x) = \sum_{j=1}^K\sigma_{ij}x_j$ and mean fitness $\bar\sigma(x) = \sum_{i,j=1}^K\sigma_{ij}x_ix_j$, the generator is

$$\mathcal Lf(x) = \frac12\sum_{i,j=1}^{K-1}x_i(\delta_{ij} - x_j)\frac{\partial^2f}{\partial x_i\partial x_j} + \sum_{i=1}^{K-1}\Bigl[\frac12(\theta_i - |\theta|x_i) + x_i\bigl(\sigma_i(x) - \bar\sigma(x)\bigr)\Bigr]\frac{\partial f}{\partial x_i}.$$

The diffusion has a unique stationary density proportional to

$$\Pi(x) = e^{\bar\sigma(x)}\prod_{i=1}^Kx_i^{\theta_i - 1},$$

and $\mathcal L$ is symmetric with respect to $\Pi$ (equation (20), with the Dirichlet weight $\prod_ix_i^{\theta_i - 1}$ of equation (13)); the authors cite Ethier and Kurtz (1994) and Barbour, Ethier and Griffiths (2000) for the stationary law. For $\sigma = 0$ it is the Dirichlet density. The selection drift is a gradient term (derivation): in the free coordinates $\partial_j\bar\sigma = 2(\sigma_j - \sigma_K)$, and $\frac12\sum_{j<K}x_i(\delta_{ij} - x_j)\,2(\sigma_j - \sigma_K) = x_i(\sigma_i - \bar\sigma)$, using $\sum_{j<K}x_j\sigma_j = \bar\sigma - x_K\sigma_K$. Well-posedness of the diffusion with diploid selection is a separate statement.

## Depends on

- [Uniqueness of the Dirichlet stationary law under parent-independent mutation](../../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion-with-mutation/dirichlet-stationary-law-under-parent-independent-mutation.md)
- [Transition density of the multi-allelic Wright–Fisher diffusion with selection](../../../../Biology/population-genetics/diffusion-theory/transition-densities-of-wright-fisher-diffusions/multi-allelic-transition-density-with-selection.md)
- [Partition function of the selection–mutation stationary density](../../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion-with-selection-and-mutat/selection-mutation-partition.md)

## Expansion

1. The generator with parent-independent mutation and diploid selection, and the mean fitness $\bar\sigma$.
2. The selection drift as half the Wright–Fisher covariance applied to the gradient of $\bar\sigma$.
3. Symmetry of $\mathcal L$ with respect to $\Pi$ by integration by parts, and stationarity of $\Pi$.
4. Uniqueness of the stationary law.
5. The case $K = 2$, where $\Pi$ is the two-allele stationary density with dominance.

## Sources

- M. Steinrücken, Y. X. R. Wang and Y. S. Song, An explicit transition density expansion for a multi-allelic Wright–Fisher diffusion with general diploid selection, Theor. Popul. Biol. 83 (2013), 1–14, Sections 2.1, 2.2 and 4, equations (1)–(3), (13) and (20). <https://doi.org/10.1016/j.tpb.2012.10.006>
