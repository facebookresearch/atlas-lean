# Only Case Prob

The probability that subject `j` of a matched set is the only case, when outcomes are
independent with `P(y_i = 1) = expit(α + β · x_i)`:
`expit(α + β · x_j) ∏_{i ≠ j} (1 - expit(α + β · x_i))`.
