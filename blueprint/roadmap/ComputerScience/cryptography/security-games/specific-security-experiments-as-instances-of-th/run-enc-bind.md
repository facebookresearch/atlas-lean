# Up-front encryption randomness under sequential composition

For `f : X → Y`, up-front randomness `ρ : Fin q → X`, an oracle computation
`c` and a continuation `g`, running `bind c g` with `ρ` from query index `i`
equals running `c` from `i` and then running `g` on its result from the query
index at which `c` stopped.
