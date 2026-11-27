# Allele-sharing kinship matrices are positive semidefinite

Let $t$ strains be genotyped at loci $j = 1, \dots, L$, locus $j$ having alleles $h = 1, \dots, H_j$. Let $l_{ijh} \ge 0$ encode the allele of strain $i$ at locus $j$: $l_{ijh} = 1$ if strain $i$ carries allele $h$ and $0$ otherwise, or, when the genotype is missing, $l_{ijh} = \sqrt{\pi_{ijh}}$ where $\pi_{ijh}$ is the probability that strain $i$ carries allele $h$ at locus $j$. Let $w_j \ge 0$ be locus weights and let $x_{hj}$, over all pairs $(h, j)$, be independent $N(0, \sigma^2)$ allele effects.

**Statement.** The genetic background effect

$$u_i = \sum_{j=1}^{L} w_j \sum_{h=1}^{H_j} l_{ijh}\, x_{hj}, \qquad i = 1, \dots, t,$$

has covariance matrix $\operatorname{Var}(u) = \sigma^2 \mathcal{K}$ with

$$\mathcal{K}_{i_0 i_1} = \sum_{j=1}^{L} w_j^2 \sum_{h=1}^{H_j} l_{i_0 jh}\, l_{i_1 jh},$$

and $\mathcal{K}$ is positive semidefinite. With $w_j = 1$ and complete genotypes, $\mathcal{K}_{i_0 i_1}$ is the number of loci at which strains $i_0$ and $i_1$ share an allele identical by state, so the simple IBS allele-sharing matrix is a valid (positive semidefinite) kinship matrix. The EMMA likelihood is then well defined and continuous for all $\delta > 0$, since all eigenvalues it uses are nonnegative.

## Depends on

- [EMMA spectral reduction of ML and REML to one variable](emma-spectral-reduction-of-ml-and-reml.md)

## Expansion

Stack the coefficients into a $t \times \sum_j H_j$ matrix $L$ with entries $w_j l_{ijh}$; then $u = Lx$ with $x \sim N(0, \sigma^2 I)$, so $\operatorname{Var}(u) = \sigma^2 L L^\top$, a Gram matrix. Any matrix of the form $LL^\top$ is positive semidefinite, regardless of whether the entries of $L$ are $0/1$ indicators or square roots of genotype probabilities. Pairwise-relatedness estimators that are not Gram matrices carry no such guarantee.

## Sources

- H. M. Kang, N. A. Zaitlen, C. M. Wade, A. Kirby, D. Heckerman, M. J. Daly and E. Eskin, "Efficient control of population structure in model organism association mapping", Genetics 178 (2008), 1709–1723, section "Similarity-based kinship matrix", Equations (10)–(11), <https://doi.org/10.1534/genetics.107.080101> (PMC2278096).
