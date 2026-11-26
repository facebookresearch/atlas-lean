# BGW gate polynomials share the correct values

Let `F` be a field and `Party` a finite type of parties, with Shamir
parameters `params`, recombination weights `lam`, and a straight-line program
`prog` over the arithmetic signature with `inputCount` inputs and `gateCount`
gates. Suppose `lam` recombines at `0`, that is `∑ i, lam i * p.eval
(params.point i) = p.eval 0` for every polynomial `p` of natural degree at
most `2 * params.threshold`, and that every input polynomial satisfies
`(inPolys k).eval 0 = x k` and `(inPolys k).natDegree ≤ params.threshold`.
Then for any randomness `tapeMul` and every gate `g`, the gate polynomial
evaluates at `0` to the value of gate `g` of `prog` on input `x`, and has
natural degree at most `params.threshold`.
