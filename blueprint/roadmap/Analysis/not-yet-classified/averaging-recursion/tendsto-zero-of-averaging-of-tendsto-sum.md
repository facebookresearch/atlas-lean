# Averaging a convergent noise series

Let `W (t + 1) = (1 - a t) * W t + a t * w t` with
gains `a t ∈ [0, 1]` whose partial sums tend to infinity. If the weighted noise series
`∑ t ∈ Finset.range n, a t * w t` converges to some `l`, then `W t` tends to `0`, for every
initial value `W 0`.
