# Bias-corrected weighted accessibility deviation (g-chromVAR)

Let $X = (x_{ij})$ be the $P \times S$ matrix of chromatin-accessibility fragment counts in peaks $i$ for samples (cell types or single cells) $j$, and $G = (g_{ik})$ the $P \times T$ matrix in which $g_{ik} \ge 0$ is the sum of the fine-mapping posterior probabilities of trait-$k$ variants lying in peak $i$. The expected counts are

$$e_{ij} = \frac{\sum_{j'} x_{ij'}}{\sum_{i'} \sum_{j'} x_{i'j'}} \sum_{i'} x_{i'j},$$

the peak's share of all fragments times the sample's total fragments in peaks. The raw weighted accessibility deviation of sample $j$ for trait $k$ is

$$y_{jk} = \frac{\sum_{i=1}^{P} x_{ij} g_{ik} - \sum_{i=1}^{P} e_{ij} g_{ik}}{\sum_{i=1}^{P} e_{ij} g_{ik}} .$$

For background sets $b = 1, \dots, B$, a $0/1$ matrix $B^{(b)}$ maps each peak to a background peak matched in GC content and average accessibility, and $y^{(b)}_{jk}$ is the same deviation computed with $B^{(b)} X$ and $B^{(b)} E$ in place of $X$ and $E$. The bias-corrected enrichment is

$$z_{jk} = \frac{y_{jk} - \operatorname{mean}_b\, y^{(b)}_{jk}}{\operatorname{sd}_b\, y^{(b)}_{jk}},$$

with a one-sided normal p-value; in Ulirsch et al. $B = 50$.

## Expansion

When $g_{ik} \in \{0, 1\}$ (a peak either carries an annotation or not) this is chromVAR's deviation score; allowing fractional weights propagates fine-mapping uncertainty, so a peak containing one variant with posterior $0.9$ counts more than one containing several weakly supported variants. Matching background peaks on GC content and accessibility (after a whitening transform of these two covariates) reproduces the technical biases of PCR amplification and Tn5 tagmentation, so the $z$-score measures excess accessibility at trait variants beyond what such biases produce. Applied to single cells, the variance of the $z$-scores within a population can be tested against its null value $1$ by a $\chi^2$ statistic, revealing heterogeneity of genetic enrichment inside classically defined progenitor populations.

## Sources

- J. C. Ulirsch, C. A. Lareau, E. L. Bao et al., "Interrogation of human hematopoiesis at single-cell and single-variant resolution", Nature Genetics 51 (2019), <https://doi.org/10.1038/s41588-019-0362-6> (PMC6441389). Online Methods, g-chromVAR methodology.
