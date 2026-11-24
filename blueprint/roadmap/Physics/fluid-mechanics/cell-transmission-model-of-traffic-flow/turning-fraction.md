# Turning fraction of a commodity between two links

Let `V` (junctions), `E` (links) and `C` (commodities) be types, `E` and `C` finite, each link `e`
running from junction `tail e` to junction `head e`, and let `q(c, e, e')` be a turning certificate:
the flow of commodity `c` from link `e` into link `e'` during one time step. The turning fraction of
commodity `c` from link `e` to link `e'` is `q(c, e, e') / ∑_{e''} q(c, e, e'')`, its share of the
outflow of `c` from `e`. With the convention `x / 0 = 0` it is `0` when that outflow is `0`.
