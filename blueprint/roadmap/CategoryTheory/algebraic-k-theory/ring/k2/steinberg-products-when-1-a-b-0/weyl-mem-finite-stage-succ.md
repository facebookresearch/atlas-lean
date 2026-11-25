# Weyl mem finite Stage succ

For `[Field F]`, `hi : i < n`, `u : Fˣ`, `weyl i n (Nat.ne_of_lt hi) u`
lies in `finiteStage (R := F) (n + 1)`. The `n + 1` bound is the minimal one
carrying both `i < n + 1` and `n < n + 1`; the statement is vacuous at
`n = 0`, characteristic-two safe, and asserts only subgroup membership, not
exact torus multiplicativity nor any boundary-torus intersection statement.
