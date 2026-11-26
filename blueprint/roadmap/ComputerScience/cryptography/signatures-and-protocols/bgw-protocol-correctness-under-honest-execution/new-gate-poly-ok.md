# A new BGW gate polynomial shares the correct value

Let `F` be a field and `Party` a finite type of parties, with Shamir
parameters `params` and recombination weights `lam`. Suppose `lam` recombines
at `0`: `∑ i, lam i * p.eval (params.point i) = p.eval 0` for every polynomial
`p` of natural degree at most `2 * params.threshold`. If every wire polynomial
`WP w` evaluates at `0` to the wire's value (input `x` or earlier gate value
`P`) and has natural degree at most `params.threshold`, then for any
randomness `tape` the new gate polynomial evaluates at `0` to the gate's value
and has natural degree at most `params.threshold`.
