# One edge upwind total salt deriv

One directed upwind edge between the boxes (generic scalar transport, not the closed
overturning loop): box 1 loses `q * S1` if `q >= 0` (flow 1 to 2) and gains `-q * S2` if
`q < 0` (flow 2 to 1), and conversely for box 2. The volume flux `|q|` carried by the edge is
assumed to return by a salt-free path, so the volumes stay fixed and only this salt flux
crosses between the boxes; in the closed loop `overturning_total_salt_deriv` the return branch
carries salt too. External forcing `F1, F2` is kept separate, so the total salt
`V1 * S1 + V2 * S2` changes only through `F1 + F2`, even when `q` changes sign.
