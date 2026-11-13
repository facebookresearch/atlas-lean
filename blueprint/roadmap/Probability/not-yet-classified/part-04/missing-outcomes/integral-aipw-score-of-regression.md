# Double robustness, regression branch

Under MAR, if the outcome regression is correct,
`m(x) = E[Y | X = x]` on covariate values of positive probability, the AIPW score is unbiased
for `E[Y]` whatever the response propensity `π` (including `π(x) = 0`, with the convention in
`aipwScore`). Positivity is not used by this identity; it is
what makes this `m` identifiable from the responders (`E[Y | X = x] = E[Y | R, X = x]`).
