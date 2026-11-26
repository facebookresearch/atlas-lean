# Marker cross-products have pedigree relationships as expectation, and ridge-regression BLUP is animal-model BLUP with the realized relationship matrix

Let $X$ be the $n \times K$ matrix of marker genotypes, $x_{ik} \in \{0, 1, 2\}$ the number of copies of a reference allele carried by individual $i$ at locus $k$, with allele frequency $p_k$ in the founder population. Treat genotypes as random given the pedigree, with $\mathbb{E}[x_{ik}] = 2p_k$ and $\operatorname{Cov}(x_{ik}, x_{jk}) = a_{ij}\, 2p_k(1 - p_k)$, where $A = (a_{ij})$ is the additive (numerator) relationship matrix.

**Proposition (Habier, Fernando and Dekkers 2007, Eqs. 2–3).** For individuals $i, j$,

$$\mathbb{E}\big[x_i^{\top} x_j\big] = \sum_{k=1}^{K} \big( a_{ij}\, 2p_k(1 - p_k) + 4p_k^2 \big), \qquad\text{so}\qquad \mathbb{E}[XX^{\top}] = A \sum_{k=1}^{K} 2p_k(1 - p_k) + \mathbf{1}\mathbf{1}^{\top} \sum_{k=1}^{K} 4p_k^2 ,$$

which is proportional to $A$ apart from a constant matrix. For independently segregating loci, $XX^{\top}/K$ converges to $\mathbb{E}[XX^{\top}]/K$ as $K \to \infty$.

**Corollary (RR–BLUP as animal-model BLUP with the realized relationship matrix).** In the ridge-regression model $y = \mathbf{1}\mu + X\beta + e$ with $\beta \sim \mathcal{N}(0, \sigma_\beta^2 I_K)$, $e \sim \mathcal{N}(0, \sigma_e^2 I_n)$ independent and

$$\sigma_\beta^2 = \frac{\sigma_a^2}{\sum_{k} 2p_k(1 - p_k)},$$

the genomic values $g = X\beta$ satisfy, for the given $X$, $\operatorname{Var}(g) = G\sigma_a^2$, $\operatorname{Cov}(g, y) = G\sigma_a^2$ and $\operatorname{Var}(y) = G\sigma_a^2 + I\sigma_e^2$, with the realized relationship matrix $G = XX^{\top}/\sum_k 2p_k(1-p_k)$. Hence, for that sample, the BLUP $X\hat\beta$ from marker effects equals exactly the BLUP $\hat g$ of the animal model $y = \mathbf{1}\mu + g + e$, $g \sim \mathcal{N}(0, G\sigma_a^2)$, which uses $G$ in place of the pedigree matrix $A$.

The pedigree matrix enters only through the expectation: by the proposition, $\mathbb{E}[G] = A + c\,\mathbf{1}\mathbf{1}^{\top}$ with $c = \sum_k 4p_k^2 / \sum_k 2p_k(1-p_k)$. Replacing $G$ by $\mathbb{E}[G]$ (or by its large-$K$ limit) gives a different model, close to the pedigree animal model with $A$, and does not preserve the predictor for a given sample: equality of two BLUPs requires matching both $\operatorname{Var}(y)$ and the target–observation covariance $\operatorname{Cov}(g, y)$, and the realized and expected matrices differ for finite $K$. What carries over is that $G$ is an unbiased (up to the constant matrix) and, as $K \to \infty$, consistent estimate of the pedigree relationships, so genomic predictions carry relationship information even when markers are in linkage equilibrium with every QTL.

## Depends on

- [Kinship coefficient](kinship.md)
- [BLUP is the conditional expectation](../linear-mixed-models-and-blup/cond-exp-mixed-model.md)

## Proof depends on

- [Second moment of genotypes in terms of kinship](integral-genotype-mul.md)
- [The GRM is unbiased for twice the kinship](integral-grm.md)

## Expansion

Each entry of $XX^{\top}$ is a sum over loci of $x_{ik}x_{jk}$, and $\mathbb{E}[x_{ik}x_{jk}] = \operatorname{Cov}(x_{ik}, x_{jk}) + \mathbb{E}[x_{ik}]\mathbb{E}[x_{jk}]$; identity by descent with probability given by the relationship coefficient produces the covariance term. Since the derivation uses only Mendelian transmission within the pedigree, no linkage disequilibrium between markers and QTL is needed: markers act as a noisy estimate of $A$. The exact BLUP equivalence holds with the realized $G$ because the BLUP of $g$ is $\operatorname{Cov}(g, y)\operatorname{Var}(y)^{-1}$ applied to the centred data (with the generalized least-squares estimate of $\mu$), and both models give the same $\operatorname{Var}(y)$ and the same $\operatorname{Cov}(g, y)$. In the paper's simulations with markers unlinked to all QTL, the accuracy of RR–BLUP genomic breeding values for sires of training animals rose from 0.5 with 100 markers to 0.78 with 2000 markers, approaching pedigree BLUP, and decayed over generations without retraining.

## Sources

- D. Habier, R. L. Fernando and J. C. M. Dekkers, "The Impact of Genetic Relationship Information on Genome-Assisted Breeding Values", Genetics 177 (2007), 2389–2397, Materials and Methods, Eqs. 1–5, <https://doi.org/10.1534/genetics.107.081190> (PMC2219482).
