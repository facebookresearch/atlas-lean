# First-order perturbation residual is of order t²

First-order perturbation: for `n ≥ 1` levels, let the unperturbed level `d 0` of the diagonal matrix
`diagonal d` be nondegenerate, `d 0 ≠ d j` for every `j ≠ 0`, and let `H1` be a real `n × n` matrix.
With the first-order corrections `E1 = (H1) 0 0` and `(v1) j = (H1) j 0 / (d 0 - d j)` for `j ≠ 0`,
`(v1) 0 = 0`, set `v(t) = e₀ + t • v1` and `E(t) = d 0 + t * E1`. Then for every `t`,
`(diagonal d + t • H1) v(t) - E(t) v(t) = t ^ 2 • (H1 v1 - E1 • v1)`: the residual is `O(t ^ 2)`.
