# Internal relocation preserves the total stock

Consider a transfer network with a finite set `V` of locations and a finite set `E` of arcs, arc `e`
running from `tail(e)` to `head(e)`. For arc flows `F`, write `(B F)(v)` for the inflow minus the
outflow at `v`: the sum of `F(e)` over arcs with `head(e) = v` minus the sum over arcs with
`tail(e) = v`. If the stock is updated by pure internal relocation, `m' = m + B F` (no additions, no
retirements), then the total stock is unchanged: `∑_v m'(v) = ∑_v m(v)`.
