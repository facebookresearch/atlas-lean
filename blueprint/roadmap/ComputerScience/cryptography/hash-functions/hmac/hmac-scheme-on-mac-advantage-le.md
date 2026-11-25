# HMAC is a secure MAC if it is a PRF

Let the chaining values `S` be finite and nonempty with decidable equality,
the messages `X` finite with decidable equality and an encoding `enc : X →
List Bool`, and the coins `R` finite and nonempty. For every forger `A` with
arbitrary coins `A.coins : PMF R`, there are coins `r` in the support of
`A.coins` such that the forgery advantage of `A` against the HMAC scheme on
`enc` is at most the PRF advantage of the deterministic distinguisher
`macReduction [] (A.forge r)` against `k, x ↦ HMAC_k(enc x)`, plus `1 / |S|`
(Katz and Lindell, Theorem 4.6 applied to HMAC as a keyed function).
