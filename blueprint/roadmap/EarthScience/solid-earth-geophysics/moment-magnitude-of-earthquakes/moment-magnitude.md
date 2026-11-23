# Moment Magnitude

Moment magnitude `Mw(M) = (2 / 3) * (log₁₀ M - c)` with zero-point `c` for
one fixed moment unit, where `log₁₀ = Real.logb 10`. It is a magnitude only for
positive moment `M`: `Real.logb` is total, so nonpositive `M` give no physical
value.
