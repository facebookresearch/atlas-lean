# Allelic test statistic

For a [case-control genotype table](total.md) $r, s$ with $R = \sum_i r_i$ cases and $S = \sum_i s_i$ controls, the allelic test statistic is [Pearson's statistic](pearson2x2.md) of the $2 \times 2$ table of allele counts with rows

$$\Bigl(\sum_i i\, r_i,\ 2R - \sum_i i\, r_i\Bigr) \quad\text{and}\quad \Bigl(\sum_i i\, s_i,\ 2S - \sum_i i\, s_i\Bigr),$$

which for nonnegative counts are the counted and other alleles among the $2R$ case alleles and the $2S$ control alleles.
