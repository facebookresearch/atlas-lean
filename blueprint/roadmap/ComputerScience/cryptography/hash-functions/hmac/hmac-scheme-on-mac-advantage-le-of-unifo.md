# MAC security of HMAC for forgers with uniform coins

Let the chaining values `S` be finite and nonempty with decidable equality,
the messages `X` finite with decidable equality and an encoding `enc : X →
List Bool`, and the coins `R` finite and nonempty. For a forger `A` whose
coins are uniform on `R`, its forgery advantage against the HMAC scheme on
`enc` is at most the PRF advantage of the keyed function `k, x ↦ HMAC_k(enc
x)` against the distinguisher `r ↦ macReduction [] (A.forge r)`, plus `1 /
|S|` (Katz and Lindell, Theorem 4.6).
