# Absolute attenuation bounds

Under exactly the hypotheses of `normalizedCovariance_attenuation`
(decomposition `X = Tx + Ex`, `Y = Ty + Ey`, square integrability,
positive true-score variances -- the observed variances are then
positive -- and the five vanishing covariances), writing
`NCov(U, V) = cov[U, V] / (sqrt Var[U] * sqrt Var[V])` for the explicit
normalized-covariance expression (notation only; no new correlation
definition), the observed normalized covariance satisfies both
attenuation bounds
`|NCov(X, Y)| <= sqrt (rhoX * rhoY)` and
`|NCov(X, Y)| <= |NCov(Tx, Ty)|`,
where `rhoX = attenuationFactor Var[Tx] Var[Ex]` and
`rhoY = attenuationFactor Var[Ty] Var[Ey]` are the reliabilities.
Both bounds are absolute: no signed comparison between `NCov(X, Y)`
and `NCov(Tx, Ty)` is asserted, since it is false for negative
covariance without a sign premise.  Zero variance is excluded only for
the true and observed scores; either error may have zero variance,
which gives that score reliability one.
