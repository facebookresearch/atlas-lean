# Share-level execution agrees with the witness polynomials

Let `F` be a field and `Party` a finite type of parties, with Shamir
parameters `params`, recombination weights `lam`, and a straight-line program
`prog` over the arithmetic signature with `inputCount` inputs and `gateCount`
gates. For every wire `w` and party `j`, the share `execShare params lam prog
x tapeIn tapeMul w j` equals the evaluation at `params.point j` of the wire's
witness polynomial: the input polynomial for an input wire and the gate
polynomial for a gate wire.
