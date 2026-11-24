# Downstream boundary flow of a commodity on a link

Let `V` (junctions), `E` (links) and `C` (commodities) be types, `E` finite, each link `e` running
from junction `tail e` to junction `head e`, and let `q(c, e, e')` be a turning certificate: the
flow of commodity `c` from link `e` into link `e'` during one time step. The downstream boundary
flow of commodity `c` on link `e` is `∑_{e'} q(c, e, e')`, the sum of its turning flows out of `e`
over all links `e'`; for a certificate supported on movements (`q(c, e, e') = 0` whenever
`head e ≠ tail e'`) only links starting at `head e` contribute.
