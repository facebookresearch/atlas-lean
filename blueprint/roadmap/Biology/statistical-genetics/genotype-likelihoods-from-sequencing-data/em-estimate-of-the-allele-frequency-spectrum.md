# EM estimation of the sample allele frequency spectrum

Let $\Phi = (\phi_0, \dots, \phi_M)$, $\sum_k \phi_k = 1$, be the sample allele frequency spectrum: the prior probability that $k$ of the $M$ sampled chromosomes carry the reference allele. At a single site with [allele-count likelihood](allele-count-likelihood-recursion.md) $\mathcal{L}(k)$, the posterior of the reference count $X$ is

$$\Pr\{X = k \mid d, \Phi\} = \frac{\phi_k\, \mathcal{L}(k)}{\sum_{l=0}^{M} \phi_l\, \mathcal{L}(l)},$$

which is used for variant calling: the posterior mass $\Pr\{X = M \mid d, \Phi\}$ that every sampled chromosome carries the reference allele measures the evidence against a variant. For $L$ independent sites with likelihoods $\mathcal{L}_a(k)$, $a = 1, \dots, L$, the EM iteration for the maximum-likelihood spectrum is

$$\phi_k^{(t+1)} = \frac{1}{L} \sum_{a=1}^{L} \frac{\phi_k^{(t)}\, \mathcal{L}_a(k)}{\sum_{l=0}^{M} \phi_l^{(t)}\, \mathcal{L}_a(l)}.$$

## Depends on

- [Likelihood of the sample allele count by dynamic programming](allele-count-likelihood-recursion.md)

## Expansion

This is EM for a finite mixture with known component likelihoods: the E-step gives the posterior of each $X_a$ and the M-step averages these posteriors over sites. The iteration preserves $\sum_k \phi_k = 1$ and does not decrease $\prod_a \sum_k \phi_k \mathcal{L}_a(k)$. A Wright–Fisher spectrum is the default prior for calling; EM-AFS replaces it when the data deviate.

## Sources

- H. Li, *A statistical framework for SNP calling, mutation discovery, association mapping and population genetical parameter estimation from sequencing data*, Bioinformatics 27 (2011), 2987–2993. <https://doi.org/10.1093/bioinformatics/btr509> (PMCID: PMC3198575) Sections 2.3.7–2.3.8, Equations (20)–(21).
