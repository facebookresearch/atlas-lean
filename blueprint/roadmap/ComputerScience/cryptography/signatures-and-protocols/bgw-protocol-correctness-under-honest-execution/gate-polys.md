# Gate sharing polynomials of a BGW program

Let `F` be a field and `Party` a finite type of parties, with Shamir
parameters `params`, recombination weights `lam`, and a straight-line program
`prog` over the arithmetic signature with `inputCount` inputs and `gateCount`
gates. Given input sharing polynomials `inPolys` and re-sharing randomness
`tapeMul`, `gatePolys` assigns a sharing polynomial to every gate; each
multiplication gate consumes one fresh re-sharing tape per party.
