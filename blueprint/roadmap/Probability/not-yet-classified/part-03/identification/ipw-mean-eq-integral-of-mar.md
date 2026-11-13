# Identification by inverse-response weighting under MAR

Under a probability law,
if the outcome is missing at random given a finitely-valued, always-observed covariate,
`R ⊥ Y | X`, and the response probability is positive, `π(x) = P(R | X = x) > 0` for every
`x` of positive probability, then
the inverse-response-weighted mean `E[1_R Y / π(X)]` (an observed-data estimand) equals the
full-data mean `E[Y]`. Only `π > 0` is needed: `π = 1` (full response in a stratum) is
allowed.
