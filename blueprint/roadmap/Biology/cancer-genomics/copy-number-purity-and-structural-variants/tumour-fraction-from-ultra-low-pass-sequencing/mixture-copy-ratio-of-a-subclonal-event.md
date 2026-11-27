# Mixture copy ratio of a subclonal copy-number event

Let a sequenced sample be a mixture in which a fraction $n \in [0, 1]$ of the DNA comes from non-tumour cells (all diploid) and $1 - n$ from tumour cells. For a clonal event of integer copy number $c$ carried by every tumour cell, the expected number of copies per genome equivalent in the mixture is

$$\mu^{\text{clonal}}(c) = 2n + (1 - n) c.$$

If instead a fraction $s \in [0, 1]$ of the tumour cells do not carry the event and retain two copies, the mixture has three components,

$$\mu^{\text{sub}}(c, s) = 2n + 2s(1 - n) + (1 - s)(1 - n) c,$$

so that $\mu^{\text{sub}}(c, 0) = \mu^{\text{clonal}}(c)$ and $\mu^{\text{sub}}(c, 1) = 2$: the quantity $1 - s$ is the fraction of tumour cells carrying the event, that is its cellular prevalence.

Normalizing by the average copy number of the sample, $2n + (1 - n)\phi$ with $\phi$ the average tumour ploidy, and taking logarithms gives the expected log copy ratio of a bin in copy-number state $c$,

$$\mu_c = \log \frac{2n + 2s(1 - n) + (1 - s)(1 - n) c}{\,2n + (1 - n)\phi\,}.$$

For fixed $c \ne 2$ and $n < 1$ the map $s \mapsto \mu^{\text{sub}}(c, s)$ is affine and moves strictly monotonically from the clonal value toward the diploid value $2$, so subclonality and low tumour fraction shift the observed ratio in the same direction: a clonal event in a sample of tumour fraction $(1-n)(1-s)$ and an event of cellular prevalence $1-s$ in a sample of tumour fraction $1-n$ have the same mixture copy number $\mu^{\text{sub}}(c, s)$, so the copy number of a single state cannot separate them. Identifiability of $(n, s)$ from copy ratios therefore requires either several states observed jointly or additional allelic information.

## Depends on

- [Average absolute copy number of a tumor sample](../../tumour-purity-ploidy-and-copy-ratio-algebra/mix-copy.md)

## Expansion

The two displayed means are the expected copy count per genome equivalent under the obvious mixture over cell populations: a sampled DNA fragment comes from a normal cell with probability $n$, from an event-free tumour cell with probability $s(1 - n)$, and from an event-carrying tumour cell with probability $(1 - s)(1 - n)$, contributing $2$, $2$ and $c$ copies respectively. Substituting $s = 0$ recovers the two-component expression. The non-identifiability is visible directly: $\mu^{\text{sub}}(c, s)$ depends on $(n, s)$ only through $2n + 2s(1-n)$ and $(1-s)(1-n)$, and for a single state $c$ the two unknowns enter one equation, so a continuum of pairs reproduces the same ratio. Fitting the mixture across many bins and several states, with a prior that penalizes solutions in which most of the genome is subclonal, is what breaks the tie in practice.

## Sources

- V. A. Adalsteinsson, G. Ha, S. S. Freeman et al., "Scalable whole-exome sequencing of cell-free DNA reveals high concordance with metastatic tumors", Nature Communications 8 (2017), 1324, Methods ("ichorCNA: copy number prediction and tumor fraction estimation", Eqs. (1) and (2) and the emission mean), <https://doi.org/10.1038/s41467-017-00965-y>, PMCID PMC5673918.
