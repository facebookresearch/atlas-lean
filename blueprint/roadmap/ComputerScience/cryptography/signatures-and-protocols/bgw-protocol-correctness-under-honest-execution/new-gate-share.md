# Share-level execution of a new BGW gate

Let `F` be a field and `Party` a finite type of parties, with Shamir
parameters `params` and recombination weights `lam`. From the share functions
`wireShare` of the argument wires and fresh randomness `tape`, `newGateShare`
gives the new gate's share function: addition is pointwise on shares, and
multiplication re-shares each party's local product and recombines the
re-sharings with `lam`.
