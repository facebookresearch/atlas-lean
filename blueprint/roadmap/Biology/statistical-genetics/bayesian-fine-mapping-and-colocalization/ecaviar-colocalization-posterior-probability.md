# eCAVIAR colocalization posterior probability

Fine-map a locus separately in a GWAS and an eQTL study, giving for each variant $i$ the posterior probabilities $\Pr(c_i^{\mathrm{GWAS}} = 1 \mid \text{data})$ and $\Pr(c_i^{\mathrm{eQTL}} = 1 \mid \text{data})$ that it is causal in each study, allowing several causal variants per study. Assuming the causal configurations of the two studies are independent, the colocalization posterior probability of variant $i$ is

$$\mathrm{CLPP}_i = \Pr(c_i^{\mathrm{GWAS}} = 1 \mid \text{data}) \cdot \Pr(c_i^{\mathrm{eQTL}} = 1 \mid \text{data}),$$

the posterior probability that variant $i$ is causal in both studies. A locus is called colocalized when some variant has $\mathrm{CLPP}_i$ above a threshold.

## Depends on

- [Posterior inclusion probability](pip.md)

## Expansion

Under independence the joint posterior of the two indicator variables factorizes, so the probability that both equal $1$ is the product of the marginal posterior inclusion probabilities. Unlike a single-causal-variant colocalization test, the marginal probabilities come from fine-mapping that allows several causal variants and accounts for linkage disequilibrium, so the product can be large only at a variant that both fine-mapping analyses support.

## Sources

- F. Hormozdiari et al., *Colocalization of GWAS and eQTL signals detects target genes*, Am. J. Hum. Genet. 99 (2016), 1245–1260. <https://doi.org/10.1016/j.ajhg.2016.10.003> (PMCID: PMC5142122)
