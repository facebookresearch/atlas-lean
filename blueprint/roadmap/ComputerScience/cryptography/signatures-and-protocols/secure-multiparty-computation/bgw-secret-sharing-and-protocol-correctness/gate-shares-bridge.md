# Gate shares agree with the gate polynomials

Let `F` be a field and `Party` a finite type of parties, with Shamir
parameters `params`, recombination weights `lam`, and a straight-line program
`prog` over the arithmetic signature with `inputCount` inputs and `gateCount`
gates. If `inShares k j = (inPolys k).eval (params.point j)` for every input
`k` and party `j`, then for any randomness `tapeMul`, every gate `g` and party
`j`, the share of gate `g` at `j` equals the evaluation at `params.point j` of
the gate polynomial built from `inPolys`.
