# Admissible weight contrasts and folded versions of neutrality tests

Under the standard neutral model with an outgroup, a [general linear neutrality test](../linear-and-optimal-neutrality-tests/general-linear-neutrality-tests-and-weight-consistent-scaling.md) is the standardized difference of two estimators $\hat\theta_\omega = \sum_{i=1}^{n-1} \omega_i\, i\,\xi_i$ and $\hat\theta_{\omega'}$ with $\sum_i \omega_i = \sum_i \omega'_i = 1$, determined by the contrast $\Omega = \omega - \omega'$, whose entries sum to $0$; the classical estimators are such linear combinations, with their weight vectors listed in Achaz (2009, Table 1). The test is defined only when this contrast has positive variance, which excludes in particular $\Omega = 0$, that is, $\omega = \omega'$. If both weight vectors are nonnegative, as for the classical estimators, the positive entries of $\Omega$ sum to at most $1$ and the negative entries to at least $-1$; conversely, every nonzero vector with zero sum and positive part at most $1$ is such a difference of two nonnegative normalized weight vectors, and it defines a neutrality test whenever its variance, computed from the covariances of the spectrum (Achaz 2009, Equation 7), is positive. Without an outgroup the same construction applies to the folded spectrum $\eta$ (Equations 10–16). An unfolded weight vector can be used on folded data exactly when the weight $i\omega_i$ on $\xi_i$ equals the weight $(n - i)\omega_{n-i}$ on $\xi_{n-i}$, that is, when $i\omega_i$ is symmetric about $n/2$ (Equations 17–20); the folded weights are then the sums of the two pooled unfolded weights. Achaz notes that Fay and Wu (2000) did not give the variance of their statistic $H$; in this framework it follows from Equation 7, and the statistic needs polarized data, since $\theta_H$ weights $\xi_i$ in proportion to $i^2$ and is not symmetric.

## Depends on

- [General linear neutrality tests and weight-consistent scaling](../linear-and-optimal-neutrality-tests/general-linear-neutrality-tests-and-weight-consistent-scaling.md)
- [Achaz's weighted estimator of $\theta$](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/theta-weighted.md)
- [Achaz's estimator is unbiased under Kingman's coalescent](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/integral-theta-weighted-kingman.md)
- [Variance of a weighted SFS estimator](../../../Biology/coalescent-theory/covariances-of-the-site-frequency-spectrum/variance-theta-weighted-kingman.md)
- [Fay and Wu's $\theta_H$](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/theta-h.md)
- [Fay and Wu's H statistic](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/fay-wu-h.md)
- [Fay and Wu's H has mean zero at constant size](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/integral-fay-wu-h.md)

## Expansion

1. The weight vector of each classical estimator and test (Table 1).
2. The constraints on $\Omega$ for nonnegative weight vectors: positive part at most $1$ and negative part at least $-1$; the converse that every such nonzero vector is a difference of two nonnegative normalized weight vectors and gives a test when its variance is positive.
3. The folded construction (Equations 10–16) and the symmetry condition for using an unfolded weight vector without an outgroup (Equations 17–20).
4. The variance of Fay and Wu's $H$ from the spectrum covariances, and the replacement of $\theta$ and $\theta^2$ by estimates in the normalization.

## Sources

- G. Achaz, Frequency spectrum neutrality tests: one for all and all for one, Genetics 183 (2009), 249–258, Model (Equations 1, 5–20) and Table 1. <https://doi.org/10.1534/genetics.109.104042>
