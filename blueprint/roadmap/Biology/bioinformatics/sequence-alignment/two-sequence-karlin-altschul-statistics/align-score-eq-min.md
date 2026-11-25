# The length bound can be cut to the pairs that exist

For a real score `s` on pairs of letters, words `u` and `v` and natural numbers `i`, `j` and `ℓ`,
the [ungapped alignment score](align-score.md) with length bound `ℓ` equals the one with length
bound `min(ℓ, |u| - i, |v| - j)` (truncated subtraction): only the pairs that exist are scored.
