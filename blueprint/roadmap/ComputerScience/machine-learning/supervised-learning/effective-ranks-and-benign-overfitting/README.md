# Effective ranks and benign overfitting

The two effective ranks $r_k$ and $R_k$ of a covariance operator, which Bartlett, Long, Lugosi
and Tsigler use to characterize when the minimum-norm interpolating estimator in linear regression
predicts nearly as well as the best linear predictor (their Theorem 4), and the elementary
relations between them (their Lemma 5).

- [Effective rank $r_k$](eff-rank.md)
- [Effective rank $R_k$](eff-rank-large.md)
- [$r_k$ is at least one](one-le-eff-rank.md)
- [$r_k^2 = r_k(\Sigma^2)\, R_k$](eff-rank-sq-eq.md)
- [$r_k(\Sigma^2) \le r_k(\Sigma)$](eff-rank-sq-le-eff-rank.md)
- [$r_k \le R_k$](eff-rank-le-eff-rank-large.md)
- [$R_k \le r_k^2$](eff-rank-large-le-eff-rank-sq.md)
- [Benign overfitting of minimum-norm interpolation in linear regression](benign-overfitting-of-minimum-norm-interpolation-in-linear-r.md)

## Supporting lemmas

- [The tail sum is at least its first term](le-tsum-tail.md)
- [The tail sum of squares is at least the first square](sq-le-tsum-sq-tail.md)
- [Tail sum of squares against the tail sum](tsum-sq-tail-le.md)

## Related topics

- [Least squares, ridge and lasso regression](../least-squares-ridge-and-lasso-regression/README.md): the regression estimators whose interpolating limit is studied here.
- [Bias–variance decomposition](../bias-variance-decomposition/README.md): the split of the excess risk into the two terms that Theorem 4 bounds separately.
- [Implicit regularization of SGD in linear models](../implicit-regularization-of-sgd-in-linear-models/README.md): stochastic gradient descent from zero, when it converges to an interpolant, converges to the minimum-norm interpolant studied here.
