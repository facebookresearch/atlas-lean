# Multi-period balance of total stock

Consider a transfer network with a finite set `V` of locations and a finite set `E` of arcs, arc `e`
running from `tail(e)` to `head(e)`. For arc flows `F`, write `(B F)(v)` for the inflow minus the
outflow at `v`: the sum of `F(e)` over arcs with `head(e) = v` minus the sum over arcs with
`tail(e) = v`. Let stocks evolve by `m(t + 1) = m(t) + B F(t) + s(t) - r(t)` for every period
`t < n`, with additions `s(t)` and retirements `r(t)`. Then after `n` periods the total stock is the
initial total plus all additions minus all retirements:
`∑_v m(n, v) = ∑_v m(0, v) + ∑_{t < n} ∑_v s(t, v) - ∑_{t < n} ∑_v r(t, v)`.
