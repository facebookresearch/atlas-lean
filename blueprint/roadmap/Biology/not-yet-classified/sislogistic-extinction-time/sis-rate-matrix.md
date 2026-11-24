# Sis Rate Matrix

The rate matrix of the SIS logistic chain on the states `0, …, N`: from `x` the chain jumps
to `x + 1` at rate `λ x (1 - x / N)` and to `x - 1` at rate `μ x`; the diagonal entry is minus
the total rate. It is a rate matrix (`IsRateMatrix`) whenever `λ, μ ≥ 0`.
