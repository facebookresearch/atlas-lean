# HMAC forgery experiment for forgers with uniform coins

Let the chaining values `S` have decidable equality,
the messages `X` have decidable equality with an encoding `enc : X → List
Bool`, and the coins `R` be finite and nonempty. For a forger `A` whose coins
are uniform on `R`, the forgery experiment of the HMAC scheme on `enc` against
`A` equals the PRF forgery experiment of the keyed function `k, x ↦ HMAC_k(enc
x)` against `A.forge`.
