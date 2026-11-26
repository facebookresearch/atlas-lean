# Communication Bound

The positive communication bound `Δ` holds on the ticks in `I` when, for every send and
receive by its intended recipient both in `I` with `sent.tick + Δ ≤ x.tick`, the occurrence is
delivered at `x.tick` or earlier. The threshold is inclusive; actual ordering and recipient
legality are supplied by `WellFormed`. Interval endpoints count exactly when they belong to `I`.
There is no delivery deadline in the absence of a qualifying receive, nor an obligation from a
send outside `I`.
