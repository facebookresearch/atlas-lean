# The storage deficit is the walk maximum of the reversed deficits

For required releases `R` and inflows `Q` over `n` time steps and every natural `t`, the
[storage deficit](required-storage-at.md) `K_t` equals the walk maximum of the time-reversed first
`t` deficits `d_{t-1}, …, d₀` (all `n` deficits when `t ≥ n`): the largest of the sums of their
initial runs, the empty sum `0` included. For `t ≤ n` this reads
`K_t = max_{0 ≤ i ≤ t} (d_i + … + d_{t-1})`.
