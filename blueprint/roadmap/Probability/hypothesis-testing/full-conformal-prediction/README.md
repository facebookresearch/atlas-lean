# Full conformal prediction

Full (transductive) conformal prediction needs no held-out calibration set. For a test covariate
$x$ and each trial response $y$, it refits the model on the augmented data
$Z_1, \dots, Z_n, (x, y)$, scores all $n + 1$ points, and keeps $y$ when the score of the trial
point is at most the $\lceil (1 - \alpha)(n + 1) \rceil$-th smallest of the other $n$ scores.
At the true response the augmented data set is the data itself. So if the data are exchangeable
and the scores are permutation equivariant (as residuals of a fitting algorithm that is
symmetric in the data are), the coverage event is the split conformal event for an exchangeable
score vector. The full conformal set therefore covers $Y_{n+1}$ with probability at least
$1 - \alpha$, and at most $1 - \alpha + 1/(n + 1)$ when there are no ties (Lei, G'Sell,
Rinaldo, Tibshirani and Wasserman, arXiv:1604.04173v2, Theorem 2.1). Both bounds hold
for any exchangeable law, which includes the i.i.d. setting of the source.

- [Permutation-equivariant score map](is-perm-equivariant.md)
- [Equivariant scores of exchangeable data are exchangeable](map-comp-perm-map-eq.md)
- [Full conformal prediction set](full-conformal-set.md)
- [Full conformal coverage event as a split conformal event](set-of-mem-full-conformal-set-eq.md)
- [Full conformal coverage](of-real-one-sub-le-measure-mem-full-conf.md)
- [Upper bound on full conformal coverage without ties](measure-mem-full-conformal-set-le.md)
- [Absolute residual score of a fitting algorithm](abs-residual-score.md)
- [Residuals of a symmetric algorithm are equivariant](is-perm-equivariant-abs-residual-score.md)

## Related topics

- [Split conformal prediction](../split-conformal-prediction/README.md): the coverage bounds for an exchangeable score vector, to which full conformal prediction reduces; split conformal prediction avoids refitting for every trial response at the price of a held-out calibration set.
- [Permutation tests](../permutation-tests/README.md): the conformal p-value of a trial response is the permutation p-value of its score among the augmented scores.
- [Negative binomial and beta-binomial distributions](../../distributions/discrete/negative-binomial-and-beta-binomial-distribution/README.md): the topic holds [product measures are exchangeable](../../distributions/discrete/negative-binomial-and-beta-binomial-distribution/sample-rank-law/map-comp-perm-pi.md), so i.i.d. data satisfy the hypothesis of the coverage theorems, and the law of the rank of a test score among i.i.d. scores.
- [Bootstrap and the Mallows metric](../../statistical-estimation/bootstrap-and-the-mallows-metric/README.md): the bootstrap gives asymptotic predictive and confidence statements under regularity conditions; conformal prediction gives finite-sample marginal coverage with none.
