# Levin

Levin's formula `Pe (RR - 1) / (1 + Pe (RR - 1))`. It is meaningful when `1 + Pe (RR - 1) ≠ 0`,
which holds for `Pe ∈ [0, 1)` and `RR ≥ 0` or for `Pe ∈ [0, 1]` and `RR > 0`; a zero denominator
gives `0` by Lean's convention `x / 0 = 0`.
