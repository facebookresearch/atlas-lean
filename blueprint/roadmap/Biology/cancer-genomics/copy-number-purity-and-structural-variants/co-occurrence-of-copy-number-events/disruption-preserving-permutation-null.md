# Disruption-preserving permutation null for co-occurrence of copy-number events

Let a cohort of $m$ samples be indexed by $j$, each sample carrying, for every chromosome, a copy-number profile. A null distribution for the co-occurrence of two recurrent events is obtained by permuting, independently for each chromosome, the assignment of that chromosome's profile to samples within a lineage, keeping genomic position and lineage fixed. This breaks dependence between events on different chromosomes while preserving each event's marginal frequency.

Such a permutation does not preserve how disrupted an individual genome is: a sample that carries many alterations genome-wide produces apparent co-occurrence of any two events. To hold that fixed, let $A_j^0$ and $D_j^0$ be the numbers of amplified and deleted markers in sample $j$ before permutation, and $A_j^t, D_j^t$ the corresponding numbers after $t$ swap steps. Define the mismatch functional

$$E_{\mathrm{tot}}(t+1) = T_{\mathrm{amp}} \sum_{j} \frac{A_j^{t+1} - A_j^{0}}{A_j^{0} + 1} \;+\; T_{\mathrm{del}} \sum_{j} \frac{D_j^{t+1} - D_j^{0}}{D_j^{0} + 1},$$

where $T_{\mathrm{amp}}, T_{\mathrm{del}} > 0$ are temperature factors increased slowly along the run and the additive $1$ in each denominator keeps the terms finite for samples with no events. Starting from a within-lineage permutation, one step picks a chromosome at random and swaps it between two randomly chosen samples of the same lineage, accepting the step with probability $1 - E_{\mathrm{tot}}$, so that configurations whose per-sample amplification and deletion burdens stay near their observed values are retained. The resulting ensemble is a permutation null conditioned on both the per-locus event frequencies and, approximately, the per-sample burden $(A_j^0, D_j^0)$.

## Depends on

- [Permutation null for copy-number scores](../../gistic-permutation-null-for-copy-number-scores/permutation-null.md)

## Expansion

The functional is a weighted $\ell^1$-type discrepancy between the current and the observed burden vectors, normalized per sample so that a deviation of a few markers counts heavily in a quiet genome and lightly in a disrupted one; raising $T_{\mathrm{amp}}$ and $T_{\mathrm{del}}$ over the run sharpens the acceptance rule toward configurations that match the observed burdens, the usual annealing schedule read in the direction of increasing stringency. The need for the construction is visible in what it changes: with only the unconstrained permutation, pairs of recurrent events appear positively correlated across a cohort merely because samples differ in overall genomic disruption, and correlations, not anticorrelations, are the ones inflated. Under the burden-preserving null the surviving signal in the analysis that motivated it was an excess of anticorrelations, which overlapped significantly with protein–protein interaction edges, whereas the correlated pairs showed no such overlap.

## Sources

- T. I. Zack, S. E. Schumacher, S. L. Carter et al., "Pan-cancer patterns of somatic copy number alteration", Nature Genetics 45 (2013), 1134–1140, Methods section 7 ("Correlation analysis", displayed equation for $E_{\mathrm{tot}}$), <https://doi.org/10.1038/ng.2760>, PMCID PMC3966983.
