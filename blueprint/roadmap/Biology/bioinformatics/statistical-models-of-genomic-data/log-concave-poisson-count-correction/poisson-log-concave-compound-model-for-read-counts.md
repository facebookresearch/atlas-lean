# Poisson log-concave compound model for read counts

**Model.** Let $x_1,\dots,x_G$ be per-base read counts along a genome. Each base $i$ has a latent log-rate $\lambda_i \in \mathbb R$, drawn independently from a density proportional to $e^{\phi(\lambda)}$ with $\phi$ a concave function (a log-concave density), and

$$x_i \mid \lambda_i \sim \mathrm{Poisson}\big(e^{\lambda_i}\big).$$

The marginal probability of a count $x$ is

$$P_\phi(x) = \frac{\displaystyle\int_{\mathbb R}\frac{e^{x\lambda}\,e^{-e^{\lambda}}}{x!}\,e^{\phi(\lambda)}\,d\lambda}{\displaystyle\int_{\mathbb R}e^{\phi(\lambda)}\,d\lambda}.$$

**Estimation.** Replacing the integrals by sums over fixed quadrature points $\lambda_1 < \dots < \lambda_Q$ with values $\phi_q = \phi(\lambda_q)$, and letting $n_x$ be the number of bases with count $x$, the maximum-likelihood problem is

$$\max_{\phi_1,\dots,\phi_Q}\ \sum_{x} n_x \log\sum_{q=1}^{Q}\frac{e^{x\lambda_q - e^{\lambda_q}}}{x!}\,e^{\phi_q} \;-\; \Big(\sum_x n_x\Big)\log\sum_{q=1}^{Q}e^{\phi_q}\quad\text{subject to } (\phi_q)\ \text{concave in } q ,$$

where concavity means $\phi_{q+1}-\phi_q$ is nonincreasing (on an equally spaced grid). It is solved by accelerated proximal gradient ascent, the proximal step being projection onto concave sequences (concave regression).

**Gradient.** The partial derivative with respect to $\phi_q$ is the expected number of bases whose latent log-rate is at grid point $q$ given their observed counts, minus the number predicted by the fitted prior alone:

$$\frac{\partial \ell}{\partial\phi_q} = \sum_x n_x\,\frac{w_{xq}e^{\phi_q}}{\sum_{q'}w_{xq'}e^{\phi_{q'}}} - \Big(\sum_x n_x\Big)\frac{e^{\phi_q}}{\sum_{q'}e^{\phi_{q'}}},\qquad w_{xq} = \frac{e^{x\lambda_q - e^{\lambda_q}}}{x!}.$$

## Remarks

The log-concave class contains most familiar unimodal densities (normal, gamma with shape at least one, and others) while excluding multimodal and very heavy-tailed laws, so it is flexible enough to capture assay-specific overdispersion yet constrained enough to be identifiable without parametric assumptions; per-base counts in ENCODE ChIP-seq, RNA-seq and DNase-seq data fit neither the Poisson, the negative binomial (gamma–Poisson) nor the log-normal–Poisson well. The gradient has the familiar EM form (posterior occupancy minus prior occupancy), but a direct EM on the latent log-rates converges slowly; the proximal method replaces it and, as the grid is refined, approaches the log-concave law closest in Kullback–Leibler divergence to the data-generating distribution. Mixtures of log-concave densities extend the model to multimodal rate distributions such as those created by copy-number variation.

## Sources

- T. B. Hashimoto, M. D. Edwards and D. K. Gifford, "Universal count correction for high-throughput sequencing", PLoS Computational Biology 10 (2014), e1003494, Results "Read counts in sequencing data are highly overdispersed" and Methods "Poisson log-concave distributions", <https://doi.org/10.1371/journal.pcbi.1003494>, PMCID PMC3945112.
