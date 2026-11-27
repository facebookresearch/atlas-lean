# Daisy-chain drive inheritance model

Consider a large population of diploid organisms carrying an engineered system spread over $n$ unlinked loci $1, \dots, n$, arranged so that the element at locus $k+1$ cuts the wild-type allele at locus $k$, while locus $n$ (the base of the chain) is cut by nothing and locus $1$ carries the cargo. At each locus there are three alleles: wild type $W$, drive element $D$, and an allele $R$ resistant to cutting.

**Germline rules.** Assume (i) a drive allele at locus $k+1$ cuts a wild-type allele at locus $k$ with probability one; (ii) $D$ and $R$ alleles are immune to cutting; (iii) a cut is repaired by homologous repair with probability $H$, copying the homologous chromosome's allele, and otherwise, with probability $1 - H$, by end joining, which creates a new $R$ allele. Then, conditional on a drive allele being present at the next locus up the chain, the genotype at locus $k$ transforms as

$$WW \mapsto RR, \qquad WR \mapsto RR, \qquad WD \mapsto \begin{cases} DD & \text{with probability } H, \\ DR & \text{with probability } 1 - H, \end{cases}$$

while $DD$, $DR$ and $RR$ are unchanged; with no drive allele at the next locus, every genotype is unchanged. Mendelian segregation then acts on the converted genotype, and the loci being unlinked, the probability of a gamete haplotype is the product of the per-locus probabilities.

**Fitness.** A drive element at locus $k$ carries a dominant fitness cost $c_k$, costs across loci acting independently, so an individual's relative fitness is $\prod_{k} (1 - c_k)^{\mathbb{1}\{\text{element } k \text{ present}\}}$. Resistance is neutral at every non-cargo locus and dominant lethal at the cargo locus, which is realized by targeting a haploinsufficient essential gene with the cargo element while carrying a recoded copy of that gene in the construct.

**Why the chain exhausts itself.** No element drives itself: locus $n$ has nothing above it and so is inherited in Mendelian fashion under a fitness cost, and is lost. Once $D$ is gone from locus $n$, locus $n-1$ stops being converted and is lost in turn, and so on up the chain, until the cargo element alone remains under its own cost and is also removed. Drive is therefore strong but temporary, and its strength grows with the number of elements: at $95\%$ homing per element, six- and seven-element chains driving a cargo of $10\%$ cost reached above $99\%$ frequency within twenty generations from a $1\%$ release, which is one to three orders of magnitude more efficient per organism released than releasing the cargo alone.

## Depends on

- [One-locus viability selection regimes](../../one-locus-selection-dynamics/one-locus-viability-selection-regimes.md)

## Expansion

The three-allele, three-rule germline model is the minimal description that keeps the two forces in tension: conversion $WD \mapsto DD$ biases transmission in favour of the element, while the end-joining branch and the fitness costs act against it, and resistance at the cargo locus is made lethal precisely so that the cargo's own non-functional escape alleles cannot take over. Independence of loci is an assumption, not a derivation; it makes the gamete distribution a product and is engineered by placing the elements on different chromosomes. The self-exhausting behaviour is a statement about the ordering of losses, driven by the fact that the chain is acyclic: cycles, which would arise if a guide RNA of an upstream element recombined into a downstream element, would turn the chain into a self-sustaining system of the kind that spreads indefinitely, which is why the construction requires sequence-divergent guide RNAs with no homology between elements.

## Sources

- C. Noble, J. Min, J. Olejarz et al., "Daisy-chain gene drives for the alteration of local populations", Proceedings of the National Academy of Sciences 116 (2019), 8275–8282, "Design and Modeling" (germline assumptions, genotype conversion rules, fitness model) and SI Appendix sections 1–2, <https://doi.org/10.1073/pnas.1716358116>, PMCID PMC6486765.
