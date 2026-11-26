# Nested continuation hash

The nested construction over the continuation hash with chaining-value keys
`k_in` and `k_out`: `H'_{k_out}(H'_{k_in}(m))`. It has the shape of NMAC
(Bellare, Canetti and Krawczyk) but is not NMAC over the full hash, whose
keyed hash pads the message alone.
