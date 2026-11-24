# Spillback: no turning flow into a link whose first cell is jammed

Let `V` (junctions), `E` (links) and `C` (commodities) be types, `E` and `C` finite, each link `e`
running from junction `tail e` to junction `head e`, and let `q(c, e, e')` be a turning certificate:
the flow of commodity `c` from link `e` into link `e'` during one time step. Suppose the certificate
is nonnegative, supported on movements (`q(c, e, e') = 0` whenever `head e ≠ tail e'`), and
satisfies the [junction-local receiving constraint](is-supply-feasible.md). If the first cell of a
link `e'` is at its jam density, `k = kj`, then `q(c, e, e') = 0` for every commodity `c` and every
link `e`: a saturated downstream link blocks all turning flow into it.
