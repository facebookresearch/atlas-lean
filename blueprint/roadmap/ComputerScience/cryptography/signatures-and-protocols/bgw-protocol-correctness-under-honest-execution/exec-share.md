# Share-level execution of a BGW program

Let `F` be a field and `Party` a finite type of parties, with Shamir
parameters `params`, recombination weights `lam`, and a straight-line program
`prog` over the arithmetic signature with `inputCount` inputs and `gateCount`
gates. Given inputs `x`, input randomness `tapeIn` and multiplication
re-sharing randomness `tapeMul`, `execShare` assigns to every wire its share
function `Party → F`.
