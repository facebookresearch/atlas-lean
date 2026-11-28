# Quality-weighted read likelihood for genotype calling

Extend the binomial mixture genotype model by treating, for each read $j$ at position $i$, the reference indicator $a_{ij}$ and the correct-alignment indicator $z_{ij}$ as latent, and observing instead the base-call quality $q_{ij} \in [0,1]$ (probability that the base call is correct) and the mapping quality $r_{ij} \in [0,1]$ (probability that the alignment is correct). Marginalizing $a_{ij}$ and $z_{ij}$, and assuming that a misaligned read carries no information (reference or not with probability $\tfrac12$), the likelihood of genotype $k$ is

$$p(q_{1:N_i}, r_{1:N_i} \mid G_i = k, \mu_k) \propto \prod_{j=1}^{N_i} \Bigl[ 0.5 (1 - r_{ij}) + r_{ij}\bigl((1 - q_{ij})(1 - \mu_k) + q_{ij} \mu_k\bigr) \Bigr],$$

for reads whose base call matches the reference; for a read showing the non-reference base, $\mu_k$ and $1 - \mu_k$ exchange roles in the bracket. The genotype posterior is $\pi_k$ times this likelihood, normalized over $k$, and the M-step of the EM fit is unchanged.

## Depends on

- [Binomial mixture genotype model with MAP-EM parameter fitting](snvmix-binomial-mixture-genotype-model.md)

## Expansion

A correctly aligned read reports the reference base either when the true allele is reference and the call is right ($q \mu_k$) or when the allele is non-reference and the call is wrong, which for a biallelic site gives $(1 - q)(1 - \mu_k)$; a misaligned read contributes the constant $\tfrac12$. Each factor therefore interpolates between the informative SNVMix1 term ($q = r = 1$) and no information ($r = 0$), soft-weighting low-quality evidence instead of discarding it. Simulations showed that calling is robust once mean base-call certainty reaches about $80\%$, suggesting that the common hard filters at Phred Q20 (99%) or Q30 (99.9%) discard usable data.

## Sources

- Goya R, Sun MG, Morin RD, Leung G, Ha G, Wiegand KC, et al. SNVMix: predicting single nucleotide variants from next-generation sequencing of tumors. *Bioinformatics* (2010), Methods, "SNVMix model specification", "Prior distributions", "Model fitting and parameter estimation" and "Modeling base and mapping qualities", equations (1)–(8). DOI <https://doi.org/10.1093/bioinformatics/btq040>. PMCID PMC2832826.
