# Minimizer sampling schemes

A minimizer (winnowing) scheme samples one $k$-mer from every window of $w$ consecutive $k$-mers of a sequence, choosing the smallest under a fixed order. Neighbouring windows usually pick the same $k$-mer, so the sample is sparse while still guaranteeing that every window is represented. The density of the scheme and the statistical behaviour of estimators computed on minimizer sketches depend on the $k$-mer order.

- [Expected density of random-order minimizers](expected-density-of-random-order-minimizers.md)
- [Density of minimizers ordered by a universal hitting set](density-of-minimizers-ordered-by-a-universal-hitting-set.md)
- [Bias and inconsistency of the minimizer Jaccard estimator](bias-and-inconsistency-of-the-minimizer-jaccard-estimator.md)
