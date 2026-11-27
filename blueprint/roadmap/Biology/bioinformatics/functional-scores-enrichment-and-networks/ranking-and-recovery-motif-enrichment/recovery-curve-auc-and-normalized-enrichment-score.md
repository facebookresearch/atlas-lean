# Recovery-curve AUC and normalized enrichment score

**Setting.** A genome has $G$ genes. A library of $N \ge 2$ motifs (or tracks) gives bijective rankings $\pi_m : \{\text{genes}\} \to \{1, \dots, G\}$, $m = 1, \dots, N$, with rank $1$ the most likely target. A query gene set $Q$ is fixed.

**Definitions.** The recovery curve of motif $m$ is

$$\mathrm{rec}_m(x) = \#\{\, g \in Q : \pi_m(g) \le x \,\}, \qquad x = 0, 1, \dots, G.$$

For a top fraction $f \in (0,1]$ (default $f = 0.03$) and $X = \lfloor f G \rfloor$, the area under the recovery curve is $\mathrm{AUC}_m = \sum_{x=1}^{X} \mathrm{rec}_m(x)$. With $\mu$ and $\sigma > 0$ the mean and standard deviation of $\mathrm{AUC}_1, \dots, \mathrm{AUC}_N$, the normalized enrichment score is

$$\mathrm{NES}_m = \frac{\mathrm{AUC}_m - \mu}{\sigma}.$$

Motifs with $\mathrm{NES}_m \ge 3$ are reported as enriched (false discovery rate between 3% and 9% in the source's benchmarks).

**Proposition.** $\mathrm{rec}_m$ is nondecreasing with $\mathrm{rec}_m(0) = 0$ and $\mathrm{rec}_m(G) = |Q|$; $0 \le \mathrm{AUC}_m \le X\,|Q|$; and $\mathrm{NES}$ is unchanged if every AUC is replaced by $\lambda\,\mathrm{AUC}_m + \kappa$ with $\lambda > 0$, so any normalization of the AUC by a common constant is immaterial.

## Remarks

Monotonicity and the bounds follow from the definition; affine invariance is the invariance of a z-score. Unlike gene set enrichment analysis, which scores many gene sets against one ranking with a Kolmogorov–Smirnov statistic, the null here is the empirical distribution of AUCs across the motif library for the *same* gene set, so motif-specific ranking biases cancel. Restricting the area to the top of the ranking emphasizes the highest-scoring regulatory regions.

## Sources

- R. Janky, A. Verfaillie, H. Imrichová, B. Van de Sande, L. Standaert, V. Christiaens, G. Hulselmans, K. Herten, M. Naval Sanchez, D. Potier, D. Svetlichnyy, Z. Kalender Atak, M. Fiers, J.-C. Marine and S. Aerts, *iRegulon: from a gene list to a gene regulatory network using large motif and track collections*, PLoS Comput. Biol. 10 (2014), e1003731. <https://doi.org/10.1371/journal.pcbi.1003731> (PMCID: PMC4109854). Materials and Methods, "Calculating motif and track enrichment on a gene set"; Fig. 1B.
