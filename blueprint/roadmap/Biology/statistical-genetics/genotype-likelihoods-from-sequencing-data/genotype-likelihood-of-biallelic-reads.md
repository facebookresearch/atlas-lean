# Genotype likelihood of biallelic sequencing reads

Fix a biallelic site and one sample of ploidy $m \ge 1$. Its genotype $g \in \{0, 1, \dots, m\}$ is the number of reference alleles among its $m$ chromosome copies. Suppose $k$ reads cover the site, the first $l$ bases ($0 \le l \le k$) equal the reference allele and the remaining $k - l$ equal the alternative allele, and let $\epsilon_j \in [0, 1]$ be the error probability of the $j$-th base. Assume that each read is drawn from one of the $m$ copies uniformly at random, that an erroneous base shows the other allele, and that errors on different reads are independent. Then the likelihood of the read data $d$ given $g$ is

$$\mathcal{L}(g) = \Pr\{d \mid g\} = \frac{1}{m^k} \prod_{j=1}^{l} \bigl[(m - g)\,\epsilon_j + g\,(1 - \epsilon_j)\bigr] \prod_{j=l+1}^{k} \bigl[(m - g)(1 - \epsilon_j) + g\,\epsilon_j\bigr].$$

For different samples the likelihoods are assumed independent, so the likelihood of all data is the product over samples.

## Expansion

A read comes from a reference copy with probability $g/m$ and from an alternative copy with probability $(m-g)/m$. A reference base is then observed with probability $1 - \epsilon_j$ or $\epsilon_j$ respectively, giving the factor $[(m-g)\epsilon_j + g(1-\epsilon_j)]/m$; the factor for an alternative base is symmetric. Independence across reads gives the product.

## Sources

- H. Li, *A statistical framework for SNP calling, mutation discovery, association mapping and population genetical parameter estimation from sequencing data*, Bioinformatics 27 (2011), 2987–2993. <https://doi.org/10.1093/bioinformatics/btr509> (PMCID: PMC3198575) Section 2.2, Equation (2); independence assumptions in Section 2.1.
