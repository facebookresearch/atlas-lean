# Composite likelihood for the selection gradient from SNP likelihoods

Let $\beta^{(i)} \in \mathbb{R}^d$ be the effects of SNP $i$ on $d$ traits and $\omega \in \mathbb{R}^d$ the vector of selection gradients. Under the multivariate Lande approximation the selection coefficient on SNP $i$ is

$$s_i \approx \sum_{j=1}^{d} \beta^{(i)}_j \omega_j = \beta^{(i)\top} \omega.$$

A neutral tag SNP with frequency $p' = 1 - q'$ and genotypic correlation $r$ to a causal SNP of frequency $p = 1 - q$ behaves as if selected with $s_{\mathrm{tag}} \approx r s \sqrt{pq / (p'q')}$, so the approximation holds for the tag with its marginal effect $\beta_{\mathrm{tag}} = \beta\, r \sqrt{pq/(p'q')}$ when the tag is in linkage disequilibrium with no other causal SNP. Given per-SNP likelihoods $L_i^{\mathrm{SNP}}(s)$ of the selection coefficient, PALM uses the composite likelihood

$$L(\omega) = \prod_{i=1}^{M} L_i^{\mathrm{SNP}}\bigl(\beta^{(i)\top} \omega\bigr)^{1/|B_i|},$$

where $B_i$ is the set of ascertained SNPs in the linkage-disequilibrium block of SNP $i$ ($|B_i| = 1$ when one SNP per block is used), and estimates $\omega$ by maximizing it. With $d = 1$ this is the marginal test; with $d > 1$ it is the joint test, whose gradients separate direct selection on a trait from correlated response through genetically correlated traits.

## Depends on

- [Polygenic adaptation](polygenic-adaptation.md)

## Expansion

The Lande approximation links fitness to allele dynamics: a unit increase in trait $j$ changes relative fitness by $\omega_j$, so an allele with effects $\beta$ has selection coefficient $\beta^\top \omega$ to first order. Each $L_i^{\mathrm{SNP}}$ is estimated by importance sampling over genealogies sampled from their neutral posterior. The exponent $1/|B_i|$ is conservative: two SNPs in perfect linkage disequilibrium contribute one likelihood factor, and two independent SNPs in the same block are down-weighted by half.

## Sources

- A. J. Stern et al., *Disentangling selection on genetically correlated polygenic traits via whole-genome genealogies*, Am. J. Hum. Genet. 108 (2021). <https://doi.org/10.1016/j.ajhg.2020.12.005> (PMCID: PMC7895848) Material and methods, "Model" (Equations 1 and 2), and Appendix A (Equations A1 and A8).
