# Aggregate conservation at a junction

Let `V` (junctions), `E` (links) and `C` (commodities) be types, `E` and `C` finite, each link `e`
running from junction `tail e` to junction `head e`, and let `q(c, e, e')` be a turning certificate:
the flow of commodity `c` from link `e` into link `e'` during one time step. If the certificate is
supported on movements (`q(c, e, e') = 0` whenever `head e ≠ tail e'`), then at every junction `v`
the total downstream boundary flow of the links ending at `v` equals the total upstream boundary
flow of the links starting at `v`, both summed over commodities. The signs of the flows are not
used. This is aggregate conservation only; it says nothing about first-in first-out order between
commodities.
