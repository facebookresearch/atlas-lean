# The radiosity matrix is strictly diagonally dominant by rows

Let `ι` be a finite set of surfaces with areas `A` and view factors `F` forming a
[black enclosure](is-black-enclosure.md) and let the emissivities satisfy `0 < ε_i ≤ 1`. Then for
every row `k` of the [radiosity matrix](radiosity-matrix.md) `M`, the sum of the absolute values of
the off-diagonal entries, `(1 - ε_k)(1 - F_{kk})`, is strictly less than
`|M_{kk}| = 1 - (1 - ε_k) F_{kk}`.
