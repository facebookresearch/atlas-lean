# Karlin–Altschul upper bound for two sequences

**Karlin–Altschul upper bound for two sequences** (the `m n e^{-λ t}` E-value bound): at a
Cramér root `θ ≥ 0` of the pair score, `P(M_{m,n} ≥ t) ≤ m n e^{-θ t}` for every `t > 0`. No
independence between diagonals is used: it is a union bound over the `m + n - 1` diagonals, each
bounded by the one-sequence estimate `SingleSequence.scoreProb_le_maxSegScore_le` through the
single-diagonal slice, and the diagonal lengths add up to `m n` (`sum_diagLen`).
