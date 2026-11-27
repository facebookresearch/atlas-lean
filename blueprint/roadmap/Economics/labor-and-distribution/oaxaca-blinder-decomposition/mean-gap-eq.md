# Two-group Oaxaca–Blinder decomposition

Coefficient convention: each group's mean
outcome equals its mean regressor vector times its own coefficient vector
(`ȳ_A = x̄_A ⬝ β_A`, `ȳ_B = x̄_B ⬝ β_B`), and group `B`'s coefficients are the reference. Then
the mean gap splits into the part explained by characteristics, `(x̄_A - x̄_B) ⬝ β_B`, and the
part due to coefficients, `x̄_A ⬝ (β_A - β_B)`. This is an accounting identity, not a causal
discrimination estimate.
