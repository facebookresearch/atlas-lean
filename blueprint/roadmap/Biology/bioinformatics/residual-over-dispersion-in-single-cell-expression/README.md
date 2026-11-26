# Residual over-dispersion in single-cell expression

In single-cell RNA-seq, a gene's biological over-dispersion is strongly confounded with its mean expression, so raw differences in variability between cell populations largely mirror differences in mean. Regressing log over-dispersion on log mean inside a hierarchical Poisson–gamma model yields a residual over-dispersion parameter that measures cell-to-cell heterogeneity free of this confounding; a geometric-mean constraint and its degenerate Gaussian prior make the spike-in-free version identifiable.

- [Residual over-dispersion regression and the differential variability test](residual-over-dispersion-regression-and-the-differential-variability-test.md)
- [Degenerate Gaussian prior under a geometric-mean identifiability constraint](degenerate-gaussian-prior-under-a-geometric-mean-identifiability-constraint.md)
