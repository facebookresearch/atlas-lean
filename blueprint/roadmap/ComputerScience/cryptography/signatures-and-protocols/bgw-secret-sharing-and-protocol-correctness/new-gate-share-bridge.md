# A new gate share agrees with its gate polynomial

Let `F` be a field and `Party` a finite type of parties, with Shamir
parameters `params` and recombination weights `lam`. If `WS w j = (WP w).eval
(params.point j)` for every wire `w` and party `j`, then for any randomness
`tape` and party `j`, `newGateShare params lam op wires WS tape j` equals the
evaluation of `newGatePoly params lam op wires WP tape` at `params.point j`.
