# Poisson expectation

`E h(Z)` for `Z` Poisson of mean `λ ≥ 0`: the integral of `h` against
`ProbabilityTheory.poissonMeasure λ`, which is `∑_w e^{-λ} λ^w / w! · h(w)`
(`ProbabilityTheory.integral_poissonMeasure`).
