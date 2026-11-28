# Spatially normalized feature vector for soft and hard sweep classification

Divide a genomic window into $n$ adjacent subwindows, with the candidate sweep site in the central subwindow. For a nonnegative population-genetic summary statistic $x$ with value $x_i$ in subwindow $i$ (and $\sum_i x_i > 0$), define its **normalized spatial profile**

$$v(x) = \Big(\frac{x_1}{\sum_{i} x_i}, \frac{x_2}{\sum_i x_i}, \dots, \frac{x_n}{\sum_i x_i}\Big) \in \Delta^{n-1},$$

a point of the probability simplex recording only the shape of the statistic across the window. The S/HIC **feature vector** of a window concatenates $v(x)$ over the statistics: nucleotide diversity $\pi$, Watterson's $\hat\theta_W$, Fay and Wu's $\hat\theta_H$, the number of distinct haplotypes, the [haplotype homozygosity statistics](h12-and-h2-h1-haplotype-homozygosity-statistics.md) $H_1$, $H_{12}$ and $H_2/H_1$, Kelly's $Z_{nS}$, and the maximum of the $\omega$ statistic. A supervised classifier (an ensemble of extremely randomized decision trees) trained on coalescent simulations assigns each window to one of five classes: hard sweep in the central subwindow, soft sweep in the central subwindow, linked to a hard sweep, linked to a soft sweep, or neutral.

**Scale invariance.** If a demographic change multiplies a statistic by a common factor $c > 0$ in every subwindow, $x_i \mapsto c\,x_i$, then $v(x)$ is unchanged. The features thus discard the absolute level of each statistic, which nonequilibrium demography strongly affects, and keep its spatial shape, which a sweep distorts in a characteristic way (a valley of diversity at the target, excess high-frequency derived alleles on the flanks, reduced haplotype diversity and elevated linkage disequilibrium on each flank but not across the target).

## Remarks

Invariance is immediate: $c x_i / \sum_l c x_l = x_i / \sum_l x_l$. Using shapes rather than values lets one classifier separate a sweep at the centre from a sweep centred in a flanking subwindow (the "soft shoulder" of a hard sweep, which can mimic a soft sweep in a single-window test): the central subwindow is the minimum of the diversity profile in the first case and not in the second. $H_{12}$ pools the two most frequent haplotypes so that a soft sweep with two common sweeping haplotypes scores as high as a hard sweep, while $H_2/H_1$ is larger when the second-most-common haplotype is frequent, separating soft from hard sweeps given high $H_{12}$. Classes are learned from simulations rather than likelihoods because the joint distribution of these statistics along a window around a sweep is analytically intractable, especially under nonequilibrium demography.

## Depends on

- [H12 and H2/H1 haplotype homozygosity statistics for hard and soft sweeps](h12-and-h2-h1-haplotype-homozygosity-statistics.md)

## Sources

- D. R. Schrider and A. D. Kern, "S/HIC: Robust Identification of Soft and Hard Sweeps Using Machine Learning", *PLoS Genetics* 12 (2016), e1005928, Methods "Supervised machine learning to detect soft and hard sweeps", <https://doi.org/10.1371/journal.pgen.1005928> (PMC4792382).
- N. R. Garud, P. W. Messer, E. O. Buzbas and D. A. Petrov, "Recent selective sweeps in North American *Drosophila melanogaster* show signatures of soft sweeps", *PLoS Genetics* 11 (2015), e1005004, <https://doi.org/10.1371/journal.pgen.1005004> (definition of $H_{12}$ and $H_2/H_1$).
