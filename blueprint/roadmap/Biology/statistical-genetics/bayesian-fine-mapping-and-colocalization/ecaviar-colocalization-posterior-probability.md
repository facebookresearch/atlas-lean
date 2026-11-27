# eCAVIAR colocalization posterior probability

Consider a locus in a GWAS and an eQTL study with marginal statistics $S^{\mathrm{GWAS}}$ and $S^{\mathrm{eQTL}}$ and causal configurations $C^{\mathrm{GWAS}}$ and $C^{\mathrm{eQTL}}$ (binary vectors with entries $c_i^{\mathrm{GWAS}}$, $c_i^{\mathrm{eQTL}}$, allowing several causal variants per study). The colocalization posterior probability of variant $i$ is the posterior probability that it is causal in both studies,

$$\mathrm{CLPP}_i = \Pr(c_i^{\mathrm{GWAS}} = 1,\ c_i^{\mathrm{eQTL}} = 1 \mid S^{\mathrm{GWAS}}, S^{\mathrm{eQTL}}).$$

Assume the two studies use independent samples, the prior causal configurations are independent, $P(C^{\mathrm{GWAS}}, C^{\mathrm{eQTL}}) = P(C^{\mathrm{GWAS}})\,P(C^{\mathrm{eQTL}})$, and each study's statistics depend only on its own configuration, $P(S^{\mathrm{GWAS}}, S^{\mathrm{eQTL}} \mid C^{\mathrm{GWAS}}, C^{\mathrm{eQTL}}) = P(S^{\mathrm{GWAS}} \mid C^{\mathrm{GWAS}})\,P(S^{\mathrm{eQTL}} \mid C^{\mathrm{eQTL}})$. Then

$$\mathrm{CLPP}_i = \Pr(c_i^{\mathrm{GWAS}} = 1 \mid S^{\mathrm{GWAS}}) \cdot \Pr(c_i^{\mathrm{eQTL}} = 1 \mid S^{\mathrm{eQTL}}),$$

where each factor is the posterior inclusion probability from fine-mapping that study alone. A locus is called colocalized when some variant has $\mathrm{CLPP}_i$ above a threshold.

## Depends on

- [Posterior inclusion probability](pip.md)

## Expansion

Under the two assumptions the joint posterior $P(C^{\mathrm{GWAS}}, C^{\mathrm{eQTL}} \mid S^{\mathrm{GWAS}}, S^{\mathrm{eQTL}})$ is proportional to $P(S^{\mathrm{GWAS}} \mid C^{\mathrm{GWAS}})P(C^{\mathrm{GWAS}}) \cdot P(S^{\mathrm{eQTL}} \mid C^{\mathrm{eQTL}})P(C^{\mathrm{eQTL}})$, so it is the product of the per-study posteriors; with only independent priors (for example with overlapping samples) it need not factorize. Hence the probability that both indicators equal $1$ is the product of the per-study posterior inclusion probabilities. Unlike a single-causal-variant colocalization test, the marginal probabilities come from fine-mapping that allows several causal variants and accounts for linkage disequilibrium, so the product can be large only at a variant that both fine-mapping analyses support.

## Sources

- F. Hormozdiari et al., *Colocalization of GWAS and eQTL signals detects target genes*, Am. J. Hum. Genet. 99 (2016), 1245–1260. <https://doi.org/10.1016/j.ajhg.2016.10.003> (PMCID: PMC5142122), Material and Methods, Equations 5–8
