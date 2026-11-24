# Inverse Prediction error le

Bounded-parameter-error transfer for inverse prediction, in the
canonical intercept-first order of `inversePrediction`. With true
intercept `a`, true slope `b`, intercept perturbation `da` bounded by
`Da`, slope perturbation `db` bounded by `Db < |b|`, observation error
`e`, observation `y = b * x + a + e`, and bounds `|x| <= X`,
`|e| <= E` (all bound constants nonnegative), the perturbed inverse
prediction `inversePrediction (a + da) (b + db) y` differs from `x`
by at most `(Db * X + Da + E) / (|b| - Db)`.
