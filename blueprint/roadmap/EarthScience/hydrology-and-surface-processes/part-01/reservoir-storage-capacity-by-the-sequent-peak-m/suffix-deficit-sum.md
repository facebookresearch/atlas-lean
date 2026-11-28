# Net deficit over a final window of steps

For required releases `R` and inflows `Q` over `n` time steps, with deficits `dᵢ = Rᵢ - Qᵢ`, and
natural numbers `i` and `t`, the suffix deficit sum is the net deficit `d_i + … + d_{t-1}`
accumulated over the steps `i, …, t - 1`. It is defined for all `i` and `t`: it is `0` when
`i ≥ t` (an empty window, the number of steps `t - i` being truncated at `0`), and steps from `n`
on contribute nothing, so for `t > n` the sum stops at `d_{n-1}`. The intended range is
`i ≤ t ≤ n`.
