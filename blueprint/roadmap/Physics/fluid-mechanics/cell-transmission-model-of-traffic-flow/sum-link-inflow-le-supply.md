# The upstream boundary flow of a link is at most its supply

Let `V` (junctions), `E` (links) and `C` (commodities) be types, `E` and `C` finite, each link `e`
running from junction `tail e` to junction `head e`, and let `q(c, e, e')` be a turning certificate:
the flow of commodity `c` from link `e` into link `e'` during one time step. If the certificate is
supported on movements (`q(c, e, e') = 0` whenever `head e ≠ tail e'`) and satisfies the
[junction-local receiving constraint](is-supply-feasible.md), then for every link `e'` the aggregate
upstream boundary flow `∑_c ∑_{e₀} q(c, e₀, e')` is at most the [receiving supply](supply.md)
`min(w (kj - k), vf w kj / (vf + w))` of the first cell of `e'`, with that link's free-flow speed
`vf`, wave speed `w`, jam density `kj` and first-cell density `k`.
