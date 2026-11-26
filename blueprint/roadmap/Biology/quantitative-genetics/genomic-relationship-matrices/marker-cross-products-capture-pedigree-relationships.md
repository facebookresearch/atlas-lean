# Marker cross-products capture pedigree relationships, so ridge-regression BLUP is animal-model BLUP

Let $X$ be the $n \times K$ matrix of marker genotypes, $x_{ik} \in \{0, 1, 2\}$ the number of copies of a reference allele carried by individual $i$ at locus $k$, with allele frequency $p_k$ in the founder population. Treat genotypes as random given the pedigree, with $\mathbb{E}[x_{ik}] = 2p_k$ and $\operatorname{Cov}(x_{ik}, x_{jk}) = a_{ij}\, 2p_k(1 - p_k)$, where $A = (a_{ij})$ is the additive (numerator) relationship matrix.

**Proposition (Habier, Fernando and Dekkers 2007, Eqs. 2–3).** For individuals $i, j$,
$$\mathbb{E}\big[x_i^{\top} x_j\big] = \sum_{k=1}^{K} \big( a_{ij}\, 2p_k(1 - p_k) + 4p_k^2 \big), \qquad\text{so}\qquad \mathbb{E}[XX^{\top}] = A \sum_{k=1}^{K} 2p_k(1 - p_k) + \mathbf{1}\mathbf{1}^{\top} \sum_{k=1}^{K} 4p_k^2 ,$$
which is proportional to $A$ apart from a constant matrix. For independently segregating loci, $XX^{\top}/K$ converges to $\mathbb{E}[XX^{\top}]/K$ as $K \to \infty$.

**Corollary (RR–BLUP as animal-model BLUP).** In the ridge-regression model $y = \mathbf{1}\mu + X\beta + e$ with $\beta \sim \mathcal{N}(0, \sigma_\beta^2 I_K)$, $e \sim \mathcal{N}(0, \sigma_e^2 I_n)$ and
$$\sigma_\beta^2 = \frac{\sigma_a^2}{\sum_{k} 2p_k(1 - p_k)},$$
one has $\operatorname{Var}(y) = XX^{\top}\sigma_\beta^2 + I\sigma_e^2$. Replacing $XX^{\top}$ by its expectation gives $\operatorname{Var}(y) = A\sigma_a^2 + c\,\mathbf{1}\mathbf{1}^{\top} + I\sigma_e^2$ with $c = \sigma_\beta^2 \sum_k 4p_k^2$, i.e. the animal model $y = \mathbf{1}\mu + Zg + e$, $g \sim \mathcal{N}(0, A\sigma_a^2)$, up to a constant shift absorbed by the overall mean. Hence the BLUP of breeding values $X\hat\beta$ from marker effects equals the BLUP $Z\hat g$ from the animal model with $A$ replaced by $XX^{\top}/\sum_k 2p_k(1-p_k)$, and genomic predictions carry relationship information even when markers are in linkage equilibrium with every QTL.

## Depends on

- [The GRM is unbiased for twice the kinship](integral-grm.md)
- [Kinship coefficient](kinship.md)
- [BLUP is the conditional expectation](../linear-mixed-models-and-blup/cond-exp-mixed-model.md)

## Expansion

Each entry of $XX^{\top}$ is a sum over loci of $x_{ik}x_{jk}$, and $\mathbb{E}[x_{ik}x_{jk}] = \operatorname{Cov}(x_{ik}, x_{jk}) + \mathbb{E}[x_{ik}]\mathbb{E}[x_{jk}]$; identity by descent with probability given by the relationship coefficient produces the covariance term. Since the derivation uses only Mendelian transmission within the pedigree, no linkage disequilibrium between markers and QTL is needed: markers act as a noisy estimate of $A$, and the BLUP equivalence follows because the mixed-model BLUP depends on the data only through the mean and covariance of $y$. In the paper's simulations with markers unlinked to all QTL, the accuracy of RR–BLUP genomic breeding values for sires of training animals rose from 0.5 with 100 markers to 0.78 with 2000 markers, approaching pedigree BLUP, and decayed over generations without retraining.

## Sources

- D. Habier, R. L. Fernando and J. C. M. Dekkers, "The Impact of Genetic Relationship Information on Genome-Assisted Breeding Values", Genetics 177 (2007), 2389–2397, Materials and Methods, Eqs. 1–5, <https://doi.org/10.1534/genetics.107.081190> (PMC2219482).
