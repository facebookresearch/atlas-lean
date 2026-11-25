# Only Case Prob

The probability that subject `j` of a matched set is the only case, when outcomes are
independent with `P(y_i = 1) = σ(α + β · x_i)`:
`σ(α + β · x_j) ∏_{i ≠ j} (1 - σ(α + β · x_i))`. Here `σ` is the logistic
function `Real.sigmoid`.
