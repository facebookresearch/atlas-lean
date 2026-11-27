# Without external sources the total stock has zero derivative

Let `s` be a finite set of compartments and `q i j t` the real transfer rate from compartment `i`
to compartment `j` at time `t`. If at time `t` every stock `m i` with `i ∈ s` has derivative
`∑ j ∈ s, (q j i t - q i j t)` (inflows minus outflows, no external source), then the total
stock `∑ i ∈ s, m i` has derivative `0` at `t`: a closed compartment system conserves its total
stock to first order.
