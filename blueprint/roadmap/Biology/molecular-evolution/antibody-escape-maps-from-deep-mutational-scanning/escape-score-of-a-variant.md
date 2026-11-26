# Escape score of a variant in a selection experiment

Let a library of barcoded protein variants be split into an antibody-selected sample and an unselected reference sample. For variant $X$ let $n_{X,\mathrm{ab}}$ and $n_{X,\mathrm{ref}}$ be its barcode counts and $N_{\mathrm{ab}}$, $N_{\mathrm{ref}}$ the totals in the two samples. The escape score of $X$ is the frequency ratio

$$E(X) = F \cdot \frac{n_{X,\mathrm{ab}} / N_{\mathrm{ab}}}{n_{X,\mathrm{ref}} / N_{\mathrm{ref}}},$$

with $F > 0$ a scaling constant chosen from the first and 99th percentiles of the raw ratios so that scores fall in $[0,1]$, values outside that range being truncated to $0$ or $1$. Variants with reference counts below a fixed minimum, or failing independent filters on folding and receptor binding, are discarded before scoring. Site-level escape at residue $m$ is the sum of the single-mutation escape scores at that site (estimated in the source by fitting global epistasis models to the variant escape scores). To reduce experimental noise in per-antibody analysis, a site is retained by the noise filter only when its total escape score is at least $0.01$ and at least $3$ times the median score of all sites.

## Expansion

The ratio of frequencies, not of raw counts, is what makes the score a selection coefficient: sequencing depth differs between the selected and reference samples, and dividing by the totals removes that difference, leaving the enrichment of $X$ relative to the library as a whole. A variant that escapes neutralization is over-represented after selection and scores near the upper limit; one that is fully neutralized is depleted and scores near zero. The scaling constant is needed because the number of cells retained after selection is not measured, so the ratio is known only up to a positive factor; fixing it by percentiles makes scores comparable across antibodies at the cost of assuming each experiment contains both escaping and non-escaping variants. The count floor controls the variance of the ratio, which is dominated by the denominator for rare barcodes, and the filters on folding and binding prevent mutations that destroy the antigen from being read as escape.

## Sources

- Cao Y, Wang J, Jian F, et al. Omicron escapes the majority of existing SARS-CoV-2 neutralizing antibodies. *Nature* 602:657-663 (2022), Methods, escape score definition. DOI <https://doi.org/10.1038/s41586-021-04385-3>. PMCID PMC8866119.
