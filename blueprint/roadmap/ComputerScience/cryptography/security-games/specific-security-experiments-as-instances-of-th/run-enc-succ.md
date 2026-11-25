# Dropping the first entry of the up-front randomness

For `f : X → Y`, `ρ : Fin (n + 1) → X`, an oracle computation `c` and an index
`i`, running `c` with `ρ` from index `i + 1` equals running `c` with the tail
of `ρ` from index `i` and adding one to the final query index.
