# Carnot volume ratio

The adiabatic legs of a reversible ideal-gas Carnot cycle force equal volume ratios:
from the MODEL hypotheses `Th * V₂ ^ k = Tc * V₃ ^ k` and `Tc * V₄ ^ k = Th * V₁ ^ k` with
`k = R / cv`, `V₂ / V₁ = V₃ / V₄`. The adiabatic relations themselves are model inputs, not
derived from the first law here. Route: `Real.log` of both relations (`Real.log_mul`,
`Real.log_rpow`), added (`linear_combination`), the factor `k ≠ 0` cancelled
(`mul_left_cancel₀`), and injectivity of `Real.log` on positives (`Real.log_injOn_pos`).
