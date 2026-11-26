# Kim–Nielsen $\omega$ statistic for the LD signature of a selective sweep

Let a genomic window contain $S \ge 4$ segregating sites in physical order, and for sites $i \ne j$ let $r_{ij}^2$ be the squared correlation (linkage disequilibrium) between their allelic states in the sample. For a split point $\ell \in \{2, \dots, S - 2\}$ let $L = \{1, \dots, \ell\}$ be the sites to the left and $R = \{\ell + 1, \dots, S\}$ those to the right. The **$\omega$ statistic** compares average LD within the two sides with average LD across them:

$$\omega_\ell = \frac{\Big(\binom{\ell}{2} + \binom{S - \ell}{2}\Big)^{-1} \Big(\sum_{i < j \in L} r_{ij}^2 + \sum_{i < j \in R} r_{ij}^2\Big)}{\big(\ell (S - \ell)\big)^{-1} \sum_{i \in L} \sum_{j \in R} r_{ij}^2}, \qquad \omega_{\max} = \max_{\ell} \omega_\ell .$$

Large values of $\omega_{\max}$, calibrated against neutral coalescent simulations with matching demography, indicate a recent selective sweep near the maximizing split.

## Depends on

- [Linkage disequilibrium of a two-locus gamete law](../../population-genetics/linkage-disequilibrium-and-haldane-s-map-functio/linkage-diseq.md)

## Expansion

During a sweep, a neutral lineage linked to the beneficial allele escapes onto the ancestral background only by recombining between itself and the selected site. Lineages on one side of the selected site share the same recombination history with respect to that side, so haplotypes that escaped on the left are carried together, producing strong LD among sites on the same side. Escape events on the left and right are independent recombinations, so sites on opposite sides are nearly uncorrelated. The expected pattern is two blocks of high LD flanking the selected site with low LD between them, which is exactly what a large ratio $\omega_\ell$ at the split near the selected site captures. Neutral regions with uniform recombination give $\omega_\ell \approx 1$. Kim and Nielsen derive the expected LD pattern genealogically, show it by simulation, and fold LD into a composite-likelihood sweep test; including LD improves power only modestly over tests using the spatial distribution and frequencies of polymorphisms alone.

## Sources

- Y. Kim and R. Nielsen, "Linkage disequilibrium as a signature of selective sweeps", Genetics 167 (2004), 1513–1524, <https://doi.org/10.1534/genetics.103.025387> (PMC1470945).
