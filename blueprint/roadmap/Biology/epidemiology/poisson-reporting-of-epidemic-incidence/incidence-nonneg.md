# Interval incidence intensity is nonnegative

For an ordered
window `a ≤ b`, reporting fraction `rho ∈ [0, 1]`, `beta ≥ 0`,
population `N > 0`, nonnegative continuous `S, I` and background
`background ≥ 0`, the real interval intensity
`rho * (∫ t in a..b, beta * S t * I t / N) + background * (b - a)`
is nonnegative, hence packages as an `NNReal` reporting intensity.
Prevalence `I(t)` is not interval incidence.
