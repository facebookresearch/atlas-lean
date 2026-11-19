# Conformalized quantile regression

Conformalized quantile regression (CQR; Romano, Patterson and Candès, NeurIPS 2019) combines the
adaptivity of quantile regression with the finite-sample validity of split conformal prediction.
Two conditional quantile functions $\hat q_{\mathrm{lo}}$ and $\hat q_{\mathrm{hi}}$, fitted on a proper training set, give a
band $[\hat q_{\mathrm{lo}}(x), \hat q_{\mathrm{hi}}(x)]$ whose width follows the local spread of the response but whose coverage
is not guaranteed. CQR calibrates it on $n$ held-out points with the conformity scores
$E_i = \max(\hat q_{\mathrm{lo}}(X_i) - Y_i, Y_i - \hat q_{\mathrm{hi}}(X_i))$, takes $Q$, the $\lceil (1 - \alpha)(n + 1) \rceil$-th smallest
score, and returns $C(x) = [\hat q_{\mathrm{lo}}(x) - Q, \hat q_{\mathrm{hi}}(x) + Q]$. If the data are exchangeable, the test
response lies in $C(X_{n+1})$ with probability at least $1 - \alpha$, and at most
$1 - \alpha + 1 / (n + 1)$ when the scores are almost surely distinct (Theorem 1). Both bounds are
corollaries of split conformal coverage applied to the score vector.

- [CQR prediction band](cqr-band.md)
- [The CQR band for a finite threshold is an interval](cqr-band-coe.md)
- [CQR conformity score](cqr-score.md)
- [CQR threshold](cqr-threshold.md)
- [CQR coverage (upper bound without ties)](measure-mem-cqr-band-le.md)
- [Membership in the CQR band through the score](mem-cqr-band-iff.md)
- [CQR coverage (lower bound)](of-real-one-sub-le-measure-mem-cqr-band.md)

## Related topics

- [Split conformal prediction](../split-conformal-prediction/README.md): CQR is split conformal prediction with the score $E_i$; its coverage bounds are those of the split conformal threshold.
