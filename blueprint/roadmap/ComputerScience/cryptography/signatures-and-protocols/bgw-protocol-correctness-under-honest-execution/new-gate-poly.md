# Sharing polynomial of a new BGW gate

Let `F` be a field and `Party` a finite type of parties, with Shamir
parameters `params` and recombination weights `lam`. For a gate with operation
`op` and argument wires `wires`, the wire polynomials `wirePoly` computed so
far and fresh re-sharing randomness `tape`, `newGatePoly` is the sharing
polynomial of the new gate. For multiplication, the re-shared secret of each
party is the product polynomial evaluated at that party's point, which equals
the product of its argument shares.
