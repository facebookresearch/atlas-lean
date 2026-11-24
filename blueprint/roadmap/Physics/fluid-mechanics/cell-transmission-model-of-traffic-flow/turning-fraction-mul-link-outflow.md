# Turning flows are turning fractions times the outflow

Let `V` (junctions), `E` (links) and `C` (commodities) be types, `E` and `C` finite, each link `e`
running from junction `tail e` to junction `head e`, and let `q(c, e, e')` be a turning certificate:
the flow of commodity `c` from link `e` into link `e'` during one time step. If the turning flows
`q(c, e, e')` of commodity `c` out of link `e` are nonnegative for every `e'`, then each equals its
[turning fraction](turning-fraction.md) times the outflow `∑_{e''} q(c, e, e'')` of `c` from `e`.
Consequently the fractions sum to one when that outflow is positive, and all the turning flows
vanish when it is zero.
