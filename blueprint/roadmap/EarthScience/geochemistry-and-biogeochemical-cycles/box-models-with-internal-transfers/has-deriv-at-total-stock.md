# Only external sources change the total stock

Let `s` be a finite set of compartments, `q i j t` the real transfer rate from compartment `i` to
compartment `j` at time `t`, and `src i t` the real external source rate into compartment `i`.
If at time `t` every stock `m i` with `i ∈ s` has derivative
`∑ j ∈ s, (q j i t - q i j t) + src i t` (inflows minus outflows plus the source), then the
total stock `∑ i ∈ s, m i` has derivative `∑ i ∈ s, src i t` at `t`: internal transfers cancel
and only external sources change the total.
