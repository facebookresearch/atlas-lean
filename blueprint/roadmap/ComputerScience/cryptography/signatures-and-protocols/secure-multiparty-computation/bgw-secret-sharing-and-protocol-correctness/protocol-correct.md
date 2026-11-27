# Correctness of honest BGW execution

Let `F` be a field and `Party` a finite type of parties, with Shamir
parameters `params` and recombination weights `lam`. Suppose `lam` recombines
at `0`: `∑ i, lam i * p.eval (params.point i) = p.eval 0` for every polynomial
`p` of natural degree at most `2 * params.threshold`. Then for every circuit
`circ` over the arithmetic signature, input `x`, randomness `tapeIn` and
`tapeMul`, and output `j`, Shamir reconstruction from all parties' output
shares equals the value of output `j` of `circ` on `x`.
