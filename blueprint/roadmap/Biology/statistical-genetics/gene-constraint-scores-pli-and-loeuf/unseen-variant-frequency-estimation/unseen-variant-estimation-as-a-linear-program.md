# Unseen-variant estimation as a linear program

Fix a finite grid $X \subset (0,1]$ of candidate population frequencies, a cohort of $k$ sampled alleles, and an observed site frequency spectrum $F_1, \dots, F_k$ ($F_i$ sites seen in exactly $i$ alleles). For nonnegative weights $w_1, \dots, w_k$, the **unseen estimator** chooses a frequency histogram $h : X \to [0,\infty)$ minimising the weighted discrepancy between the expected and observed spectra,

$$\min_{h \ge 0}\ \sum_{i=1}^{k} w_i \,\Big| F_i - \sum_{x \in X} h(x)\,\mathrm{bin}(x,k,i) \Big|, \qquad \mathrm{bin}(x,k,i) = \binom{k}{i}x^i(1-x)^{k-i},$$

possibly with linear side constraints (for example a fixed total number of sites, or $h(x) = 0$ above a frequency threshold where the empirical spectrum is used directly). This is a linear program: introducing slack variables $e_i$ with

$$e_i \ge F_i - \sum_x h(x)\,\mathrm{bin}(x,k,i), \qquad e_i \ge \sum_x h(x)\,\mathrm{bin}(x,k,i) - F_i,$$

the problem becomes minimising $\sum_i w_i e_i$ over the polyhedron in $(h, e)$, which has an optimal vertex and can be solved in polynomial time. The fitted $h$ includes mass at frequencies below $1/k$, the variants not yet observed, and plugging it into the discovery curve $\sum_x h(x)(1 - (1-x)^N)$ extrapolates the number of distinct variants a cohort of $N > k$ alleles will see.

## Depends on

- [Expected frequency spectrum and discovery curve of a variant-frequency histogram](expected-frequency-spectrum-and-discovery-curve.md)
- [Binomial probability mass function](../../../cancer-genomics/detection-power-for-somatic-mutations/binom-pmf.md)
- [A linear program attaining its minimum attains it at a basic point](../../../../Geometry/convex-geometry/linear-programming/basic-feasible-solutions/exists-basic-optimal.md): the optimal vertex

## Expansion

Each expected count is linear in $h$, so each absolute deviation is a convex piecewise-linear function of $h$, and the epigraph reformulation is exact. No prior distribution of frequencies, demographic model or selection model enters; the grid $X$ and the constraints are the only modelling choices. The spectrum constrains $h$ only through its first $k$ moments, so many histograms fit equally well; the linear program picks one, and the reliability of an extrapolation decreases with the ratio $N/k$. Zou et al. (UnseenEst) contrast this with the third-order jackknife, which predicts the count in $N$ alleles directly as $g_1 F_1 + g_2 F_2 + g_3 F_3$ without estimating $h$. They validated UnseenEst by fitting the spectrum of a random tenth of the ExAC alleles and predicting the frequency distribution and discovery rates of the full cohort of 60,706 exomes, then predicted that sequencing $500{,}000$ randomly chosen individuals would reveal over $12\%$ of all possible missense variants and $7.5\%$ of all possible loss-of-function variants.

## Sources

- J. Zou et al., "Quantifying unobserved protein-coding variants in human populations provides a roadmap for large-scale sequencing projects", Nature Communications 7 (2016), 13293, <https://doi.org/10.1038/ncomms13293> (PMC5095512), Results, "Quantifying unobserved protein-coding variants", and Methods, "UnseenEst algorithm".
- G. Valiant, P. Valiant, "Estimating the unseen: improved estimators for entropy and other properties", Advances in Neural Information Processing Systems 26 (2013).
