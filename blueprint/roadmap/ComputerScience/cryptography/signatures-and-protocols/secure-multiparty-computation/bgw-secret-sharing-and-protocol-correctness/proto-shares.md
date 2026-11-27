# Output shares of a BGW execution

Let `F` be a field and `Party` a finite type of parties, with Shamir
parameters `params` and recombination weights `lam`. For a circuit `circ` over
the arithmetic signature, inputs `x`, input randomness `tapeIn` and
multiplication randomness `tapeMul`, `protoShares params lam circ x tapeIn
tapeMul j` gives every party's share of output `j`.
