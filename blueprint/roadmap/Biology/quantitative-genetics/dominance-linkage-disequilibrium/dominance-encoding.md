# Dominance encoding of a biallelic genotype

For real numbers $p$ and $g$, the dominance encoding is

$$\eta_p(g) = \begin{cases} p^2 & g = 0,\\ -p(1 - p) & g = 1,\\ (1 - p)^2 & \text{otherwise}. \end{cases}$$

For a genotype $g \in \{0, 1, 2\}$ counting the allele of frequency $p$, and $0 < p < 1$, dividing by $-p(1 - p)$ gives the encoding $-p/(1 - p)$, $1$, $-(1 - p)/p$ of Palmer et al. (2023).

## Sources

- D. S. Palmer, W. Zhou, L. Abbott, E. M. Wigdor, N. Baya, C. Churchhouse, C. Seed, T. Poterba, D. King, M. Kanai, A. Bloemendal, B. M. Neale, *Analysis of genetic dominance in the UK Biobank*, Science 379 (2023), 1341–1348.
