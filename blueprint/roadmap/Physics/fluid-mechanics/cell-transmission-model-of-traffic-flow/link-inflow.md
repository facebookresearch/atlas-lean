# Upstream boundary flow of a commodity on a link

Let `V` (junctions), `E` (links) and `C` (commodities) be types, `E` and `C` finite, each link `e`
running from junction `tail e` to junction `head e`, and let `q(c, e, e')` be a turning certificate:
the flow of commodity `c` from link `e` into link `e'` during one time step. The upstream boundary
flow of commodity `c` on link `e` is `∑_{e₀} q(c, e₀, e)`, the sum of its turning flows into `e`
over all links `e₀`; for a certificate supported on movements (`q(c, e, e') = 0` whenever
`head e ≠ tail e'`) only links ending at `tail e` contribute.
