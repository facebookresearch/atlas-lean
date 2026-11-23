# Total salt with one upwind edge changes only by forcing

Two boxes of positive volumes `V1` and `V2` are joined by one directed upwind edge carrying the
transport `q`: box 1 loses `q S1` to box 2 if `q ≥ 0` and gains `-q S2` from box 2 if `q < 0`,
and conversely for box 2. If at a time `t` the salinities are differentiable with
`V1 S1'(t) = -q S1(t) + F1` and `V2 S2'(t) = q S1(t) + F2` when `q ≥ 0`, and with
`V1 S1'(t) = -q S2(t) + F1` and `V2 S2'(t) = q S2(t) + F2` when `q < 0`, then the total salt
`V1 S1 + V2 S2` has derivative `F1 + F2` at `t`, whatever the sign of `q`. The volumes stay
fixed only if the volume flux `|q|` returns by a salt-free path; this is generic upwind scalar
transport, not the closed overturning loop, whose return branch carries salt too.
