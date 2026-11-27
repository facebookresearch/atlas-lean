# Every ungapped alignment scores at most the maximal alignment score

For a real score `s` on pairs of letters, words `u` and `v` and natural numbers `i ≤ |u|`,
`j ≤ |v|` and `ℓ ≤ |u|`, the [ungapped alignment score](align-score.md) of `u` from `i` with `v`
from `j` with length bound `ℓ` is at most the
[maximal ungapped alignment score](max-align-score.md) of `u` and `v`.
