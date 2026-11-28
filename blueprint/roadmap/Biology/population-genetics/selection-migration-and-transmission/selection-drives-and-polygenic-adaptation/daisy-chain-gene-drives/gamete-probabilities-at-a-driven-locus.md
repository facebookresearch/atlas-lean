# Gamete probabilities at a driven locus

Take one locus of a [daisy-chain drive](daisy-chain-drive-inheritance-model.md) whose upstream element is present, so that cutting occurs, with homologous repair probability $H \in [0, 1]$ and end joining probability $1 - H$. Let the locus carry alleles among $\{W, D, R\}$.

**Heterozygote $WD$.** The wild-type allele is cut and repaired, giving $DD$ with probability $H$ and $DR$ with probability $1 - H$; segregation then gives the gamete probabilities

$$\Pr(D) = \frac{1 + H}{2}, \qquad \Pr(R) = \frac{1 - H}{2}, \qquad \Pr(W) = 0 .$$

**Other genotypes.** $WW$ and $WR$ are converted to $RR$, so they transmit $R$ with probability one; $DD$, $DR$ and $RR$ transmit their alleles in Mendelian proportions $1$, $(1/2, 1/2)$ and $1$ respectively. With no drive allele at the next locus, every genotype transmits in Mendelian proportions.

**Transmission bias.** The transmission probability of $D$ from a heterozygote is $(1 + H)/2 \in [1/2, 1]$, strictly above the Mendelian $1/2$ for $H > 0$ and equal to one only for perfect homing. Equivalently the bias is $(1+H)/2 - 1/2 = H/2$, and the wild-type allele is never transmitted from a cut heterozygote: every failed conversion produces a resistant allele rather than restoring $W$. Measured homing probabilities in the organisms where such systems have been built span roughly $H \in [0.37, 0.998]$, so the transmission advantage per generation ranges from modest to nearly complete.

Multiplying over unlinked loci, the probability that an individual produces a given multilocus haplotype is the product of these per-locus probabilities, each evaluated with the conversion rule switched on or off according to whether the next locus up the chain carries a drive allele in that individual.

## Depends on

- [Daisy-chain drive inheritance model](daisy-chain-drive-inheritance-model.md)

## Expansion

The three numbers $\big((1+H)/2, (1-H)/2, 0\big)$ are the whole mechanism of homing drive in one line: conversion turns a heterozygote into a homozygote before meiosis, so the biased ratio is a consequence of changing the genotype, not of biased segregation. The asymmetry between the two repair outcomes matters more than its magnitude: because end joining yields $R$ rather than $W$, the wild-type allele is consumed irreversibly, and a population under sustained cutting converges to a mixture of $D$ and $R$ with no $W$ left. That is why resistance accumulates even when $H$ is high, and why the cargo locus is engineered so that $R$ is lethal — otherwise $R$, which pays no cost and cannot be cut, outcompetes both the cargo and the wild type.

## Sources

- C. Noble, J. Min, J. Olejarz et al., "Daisy-chain gene drives for the alteration of local populations", Proceedings of the National Academy of Sciences 116 (2019), 8275–8282, "Design and Modeling" (gamete probabilities $(1+H)/2$ and $(1-H)/2$; reported homing efficiencies) and SI Appendix Eq. 7, <https://doi.org/10.1073/pnas.1716358116>, PMCID PMC6486765.
