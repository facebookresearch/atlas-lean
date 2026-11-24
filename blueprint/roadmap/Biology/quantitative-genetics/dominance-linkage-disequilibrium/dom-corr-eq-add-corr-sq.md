# Dominance LD is the square of additive LD

For every [two-locus genotype under random union](random-union.md) (independent, identically distributed, square-integrable haplotypes) on a probability measure $P$,

$$\frac{\int d_A d_B \, dP}{\sqrt{\int d_A^2 \, dP \int d_B^2 \, dP}} = \Bigl(\frac{\int a_A a_B \, dP}{\sqrt{\int a_A^2 \, dP \int a_B^2 \, dP}}\Bigr)^2,$$

where $a_A, a_B$ are the [additive codings](add-a.md) and $d_A, d_B$ the [dominance codings](dom-a.md), with the convention $x/0 = 0$: the correlation of the dominance codings at two loci is the square of the correlation of their additive codings (Palmer et al. 2023).

## Sources

- D. S. Palmer, W. Zhou, L. Abbott, E. M. Wigdor, N. Baya, C. Churchhouse, C. Seed, T. Poterba, D. King, M. Kanai, A. Bloemendal, B. M. Neale, *Analysis of genetic dominance in the UK Biobank*, Science 379 (2023), 1341–1348.
