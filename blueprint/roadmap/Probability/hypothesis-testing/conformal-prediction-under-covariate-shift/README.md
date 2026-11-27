# Conformal prediction under covariate shift

Conformal prediction needs the calibration and test points to be exchangeable. Under covariate
shift the covariate law changes between training ($P_X$) and test ($\tilde P_X$) while the conditional
law of the response stays the same, and exchangeability fails. Tibshirani, Barber, Candès and
Ramdas (NeurIPS 2019) restore finite-sample coverage by reweighting: with the likelihood ratio
$w = d\tilde P_X / dP_X$, the calibration scores get weights $p_i(x) = w(X_i) / (\sum_j w(X_j) + w(x))$,
the remaining mass $p_{n+1}(x)$ is placed at $+\infty$, and the threshold is the level-$(1 - \alpha)$
quantile of this weighted distribution. Its coverage is at least $1 - \alpha$ (Corollary 1), a
consequence of a weighted quantile lemma for weighted-exchangeable data. The pages below treat the weighted quantile, its coverage criterion and the coverage theorem for split (fixed) score functions.

- [Weighted split conformal coverage under covariate shift](le-measure-score-le-weighted-quantile.md)
- [Criterion for lying below the weighted quantile](coe-le-weighted-quantile-iff.md)
- [Weighted quantile with an atom at $+\infty$](weighted-quantile.md)
- [The weighted quantile is infinite exactly when the finite weight is short](weighted-quantile-eq-top-iff.md)

## Related topics

- [Split conformal prediction](../split-conformal-prediction/README.md): the unshifted case $w \equiv 1$, where the weighted quantile is the $\lceil (1 - \alpha)(n + 1) \rceil$-th smallest calibration score.
- [Conformalized quantile regression](../conformalized-quantile-regression/README.md): another split conformal method; its scores can be used in the weighted procedure.
