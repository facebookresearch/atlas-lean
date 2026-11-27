# Standardized index of association

Let $n \ge 2$ haploid isolates be typed at $l \ge 2$ loci, let $p_{ij}$ be the sample frequency of allele $i$ at locus $j$, and let

$$h_j = \frac{n}{n-1}\Bigl(1 - \sum_i p_{ij}^2\Bigr)$$

be the unbiased gene diversity at locus $j$. For a pair of isolates let $D$ be the number of loci at which they carry different alleles, and let $V_D$ be the variance of $D$ over all $M = \binom{n}{2}$ pairs (population variance with divisor $M$, corresponding to a uniformly sampled pair; LIAN v3.7 uses the sample-variance divisor $M - 1$ for $V_D$ while leaving $V_e$ unchanged). Under linkage equilibrium the expected variance is

$$V_e = \sum_{j=1}^{l} h_j (1 - h_j).$$

When $V_e > 0$ (i.e. at least one locus is polymorphic with $0 < h_j < 1$), the standardized index of association is defined as

$$I_A^S = \frac{1}{l - 1}\Bigl(\frac{V_D}{V_e} - 1\Bigr),$$

and is undefined when $V_e = 0$. When defined, $I_A^S \approx 0$ under random association of alleles across loci, and $I_A^S > 0$ indicates multilocus linkage disequilibrium, as produced by clonal propagation or population structure. Significance is assessed by comparing $V_D$ with its distribution when alleles are permuted independently among isolates at each locus.

## Expansion

Write $D = \sum_j D_j$ with $D_j$ the mismatch indicator at locus $j$; for a random pair $\Pr(D_j = 1) = h_j$, so $\operatorname{Var}(D_j) = h_j(1 - h_j)$. Under independence across loci the covariances vanish and $\operatorname{Var}(D) = V_e$; any excess $V_D - V_e$ is the sum of between-locus covariances of mismatch indicators. The unstandardized index $I_A = V_D/V_e - 1$ grows with the number of loci, and dividing by $l - 1$ (the number of covariance terms per variance term) makes values comparable across marker sets. In malaria genetic surveillance with a 24-SNP barcode of single-strain infections, the source used $I_A^S$ (10,000 permutations) together with the frequency of identical barcodes to show increasing clonal transmission in Senegal after enhanced malaria control.

## Sources

- R. Daniels, H.-H. Chang, P. D. Séne, D. C. Park, D. E. Neafsey, S. F. Schaffner, et al., "Genetic surveillance detects both clonal and epidemic transmission of malaria following enhanced intervention in Senegal", *PLoS ONE* 8 (2013), e60780, Methods (index of association), <https://doi.org/10.1371/journal.pone.0060780> (PMC3617153).
- B. Haubold and R. R. Hudson, "LIAN 3.0: detecting linkage disequilibrium in multilocus data", *Bioinformatics* 16 (2000), 847–849, <https://doi.org/10.1093/bioinformatics/16.9.847>.
