# Bernoulli Null LR

Null likelihood-ratio process for testing success probability `q` against the fixed
reference alternative `p0`: product of per-observation alternative-over-null ratios over
observations `X_0..X_n` (inclusive product over `range (n + 1)`, matching the inclusive
`Filtration.natural`; an exclusive product over `range n` would be one step ahead of the
filtration and is unsound here).
