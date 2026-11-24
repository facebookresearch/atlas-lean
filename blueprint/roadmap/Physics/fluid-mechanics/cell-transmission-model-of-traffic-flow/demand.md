# Sending demand min(v k, capacity) of a cell

For a free-flow speed `v`, a wave speed `w`, a jam density `kj` and a cell density `k` (real
numbers), the sending demand of the cell is `min(v k, v w kj / (v + w))`: the free-flow flow `v k`
capped at the [capacity](capacity.md) of the triangular fundamental diagram. In the physical reading
`v`, `w`, `kj` are positive and `0 ≤ k ≤ kj`; the definition takes any real values.
