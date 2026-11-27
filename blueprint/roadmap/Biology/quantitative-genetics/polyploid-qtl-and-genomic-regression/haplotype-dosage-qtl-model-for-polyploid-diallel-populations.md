# Haplotype-dosage QTL model and IBD relationships for polyploid diallel populations

Consider a diallel (a set of connected F1, and possibly selfed S1, populations) derived from $p$ outbred parents of ploidy $\phi$, so that there are $\phi p$ **parental haplotypes**, indexed by $k$. At locus $j$ each offspring (clone) $i$ carries one of finitely many parental genotype states $abcd$ (a multiset of $\phi$ parental haplotypes; $100$ states in a biparental tetraploid F1, $35$ in a tetraploid S1), with posterior probability $P_{ij}(abcd)$ from a hidden Markov model of inheritance. Let $w_k(abcd)$ be the number of copies of haplotype $k$ in $abcd$, and $w_{kk'}(abcd)$ the number of the $\binom{\phi}{2}$ unordered pairs of homologs in $abcd$ that form the **diplotype** $kk'$. The expected dosages are

$$W_{ijk} = \sum_{abcd} w_k(abcd)\, P_{ij}(abcd), \qquad W_{ijkk'} = \sum_{abcd} w_{kk'}(abcd)\, P_{ij}(abcd).$$

**QTL model.** For measurement $t$ of clone $i$, with $m$ QTL,

$$y_{it} = \mu + x_{it} c + \sum_{j=1}^{m} \sum_{k=1}^{\phi p} W_{ijk}\, \alpha_{jk} + \sum_{j} \sum_{k \le k'} W_{ijkk'}\, \beta_{jkk'} + \epsilon_{it},$$

where $\alpha_{jk}$ are additive effects of parental haplotypes and $\beta_{jkk'}$ digenic dominance effects of parental diplotypes, both random with BayesC (point-mass–normal mixture) priors and constrained to sum to zero at each locus. Additive $\times$ additive epistasis uses two-locus dosages $W_{ijkj'k'} = \sum_{abcd}\sum_{a'b'c'd'} w_k(abcd)\, w_{k'}(a'b'c'd')\, P_{ij}(abcd)\, P_{ij'}(a'b'c'd')$. The average of a parent's haplotype effects is its general combining ability (GCA), so QTL are detected by comparing this model with a GCA-only null via $-\Delta\mathrm{DIC}$, with a stratified permutation threshold.

**IBD relationship matrices.** Averaging over $m$ loci, the additive relationship ($\phi$ times the probability that random homologs of $i$ and $i'$ are IBD) and the digenic dominance relationship are

$$A_{ii'} = \frac{1}{\phi m} \sum_{j=1}^{m} \sum_{k=1}^{\phi p} W_{ijk} W_{i'jk}, \qquad D_{ii'} = \binom{\phi}{2}^{-1} \frac{1}{m} \sum_{j=1}^{m} \sum_{k \le k'} W_{ijkk'} W_{i'jkk'},$$

which supply covariances of polygenic random effects (computed leaving out the chromosome under test).

## Related topics

- [Genomic relationship matrices](../genomic-relationship-matrices/README.md): the diploid, biallelic relationship matrices that the haplotype-based IBD relationship matrices generalize.

## Expansion

Because all populations share parents, each parental haplotype is a single allele of a multiallelic QTL whose effect is estimated jointly across populations. The dosage $W_{ijk}$ is the expected number of copies of haplotype $k$ at the locus, so the additive term is linear regression on expected dosage. In a polyploid, dominance acts on pairs of homologs, giving $\binom{\phi}{2}$ digenic interactions per genotype; this is why diplotype counts $w_{kk'}$ enter. For $A_{ii'}$: a random homolog of $i$ is haplotype $k$ with probability $W_{ijk}/\phi$, so the IBD probability at locus $j$ is $\sum_k (W_{ijk}/\phi)(W_{i'jk}/\phi)$, and multiplying by $\phi$ and averaging over loci gives the formula. $D_{ii'}$ follows the same way for random pairs of homologs, with probability $W_{ijkk'}/\binom{\phi}{2}$, multiplied by $\binom{\phi}{2}$. For $\phi = 2$ these reduce to the usual diploid IBD-based additive and dominance relationships.

## Sources

- R. R. Amadeu, P. R. Muñoz, C. Zheng and J. B. Endelman, "QTL mapping in outbred tetraploid (and diploid) diallel populations", Genetics 219 (2021), iyab124, Materials and methods (Equations 1–9 and "Model selection"), <https://doi.org/10.1093/genetics/iyab124> (PMC8570786).
