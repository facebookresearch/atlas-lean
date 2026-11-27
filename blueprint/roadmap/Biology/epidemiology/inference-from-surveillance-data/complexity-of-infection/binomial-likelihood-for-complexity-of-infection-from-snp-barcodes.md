# Binomial likelihood for complexity of infection from SNP barcodes

**Model.** A sample contains $C \in \{1, 2, \dots\}$ haploid parasite lineages drawn independently from the population. A barcode consists of biallelic assays $i = 1, \dots, A$ with alternate-allele frequency $p_i \in (0, 1)$, in linkage equilibrium with one another. For assay $i$ the number of lineages carrying the alternate allele is

$$X_i \mid C \sim \operatorname{Binomial}(C, p_i),$$

and the assay reports one of three outcomes: reference only ($X_i = 0$), alternate only ($X_i = C$), or polymorphic ($0 < X_i < C$). Hence

$$\mathbb P(\text{ref} \mid C) = (1 - p_i)^C, \quad \mathbb P(\text{alt} \mid C) = p_i^C, \quad \mathbb P(\text{poly} \mid C) = 1 - (1 - p_i)^C - p_i^C .$$

**Genotyping error.** Let $E$ be a $3 \times 3$ row-stochastic matrix with $E_{gh} = \mathbb P(\text{observed } h \mid \text{true } g)$. The probability of an observed outcome $h$ is $\mathbb P(G_i^* = h \mid C) = \sum_g \mathbb P(G_i = g \mid C)\,E_{gh}$.

**Posterior.** With a prior $\pi(C)$ on $\{1, \dots, C_{\max}\}$ (uniform up to the barcode's detection limit by default), assay independence gives

$$\mathbb P(C \mid G^*) = \frac{\pi(C)\prod_{i} \mathbb P(G_i^* \mid C)}{\sum_{C'} \pi(C')\prod_{i} \mathbb P(G_i^* \mid C')},$$

where failed assays are omitted from the product. The maximum a posteriori value and a credible set summarize the sample's COI. If $p_i$ is unknown it is estimated from presumed single infections (samples with no polymorphic calls) under a $\operatorname{Beta}(1, 1)$ prior, giving $\hat p_i = (k_i + 1)/(n_i + 2)$ for $k_i$ alternate calls among $n_i$ single infections.

**Discriminating power.** For a single error-free assay, $\mathbb P(\text{poly} \mid C)$ increases strictly with $C$ and, for fixed $C \ge 2$, is maximized at $p_i = 1/2$; so assays with high minor-allele frequency and more assays both separate the distributions of the number of polymorphic calls across COI levels.

**Correlated assays.** If $X = \sum_{i=1}^n B_i$ with $B_i \sim \operatorname{Bernoulli}(p)$ and pairwise correlations $\rho_{ij}$, then $\mathbb E X = np$ and

$$\operatorname{Var} X = np(1 - p) + p(1 - p)\sum_{i \ne j}\rho_{ij},$$

so linkage disequilibrium between assays overdisperses the polymorphic-call count and makes single-sample COI estimates more extreme while leaving population averages approximately unbiased. Relatedness between co-infecting lineages instead makes monomorphic calls more likely and biases COI estimates downward, with no balancing effect.

## Expansion

Each lineage independently carries the alternate allele with probability $p_i$, which gives the binomial law and the three outcome probabilities. The error model is a hidden-state channel: summing over the true outcome gives the observed-outcome probabilities. Independence across assays turns the barcode likelihood into a product, and Bayes' rule over the finite set of COI values gives the posterior. For monotonicity, $\mathbb P(\text{poly} \mid C+1) - \mathbb P(\text{poly} \mid C) = p_i(1 - p_i)^C + (1 - p_i)p_i^C > 0$. For fixed $C$, $(1-p)^C + p^C$ is convex and symmetric about $1/2$, hence minimized there. The variance formula is the variance of a sum, with $\operatorname{Cov}(B_i, B_j) = \rho_{ij}p(1 - p)$.

## Sources

- K. Galinsky, C. Valim, A. Salmier, B. de Thoisy, L. Musset, E. Legrand, A. Faust, M. L. Baniecki, D. Ndiaye, R. F. Daniels, D. L. Hartl, et al., *COIL: a methodology for evaluating malarial complexity of infection using likelihood from single nucleotide polymorphism data*, Malaria Journal 14 (2015), 4, <https://doi.org/10.1186/1475-2875-14-4>, PMCID PMC4417311. Methods (binomial model of alternate-allele counts, three assay outcomes, error matrix, posterior with uniform prior up to COI five, Beta(1,1) allele-frequency prior) and Discussion (variance of correlated Bernoulli sums; overdispersion and unbiased population estimates under assay non-independence; downward bias of COI under relatedness of co-infecting lineages). The monotonicity statements are derived here.
