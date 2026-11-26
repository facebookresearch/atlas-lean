# Share-level execution of the gates of a BGW program

Let `F` be a field and `Party` a finite type of parties, with Shamir
parameters `params`, recombination weights `lam`, and a straight-line program
`prog` over the arithmetic signature with `inputCount` inputs and `gateCount`
gates. Given input share functions `inShares` and re-sharing randomness
`tapeMul`, `gateShares` assigns to every gate its share function `Party → F`.
