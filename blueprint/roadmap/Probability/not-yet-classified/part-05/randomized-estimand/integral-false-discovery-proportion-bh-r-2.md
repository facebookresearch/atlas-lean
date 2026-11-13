# BH FDR control in a randomized trial (treatment independent of the potential outcomes)

If the treatment indicator is independent of the potential outcomes of every endpoint with zero
average treatment effect, `0 < P(T) < 1`, and the independent p-values
are calibrated for the observed-data Horvitz–Thompson null (`ipwContrast_const`), BH at level
`q ∈ [0, 1]` has FDR at most `q |ateNulls| / m` over the endpoints with zero average treatment
effect. Randomization enters through `stronglyIgnorable_of_indepFun`. No power claim is made.
