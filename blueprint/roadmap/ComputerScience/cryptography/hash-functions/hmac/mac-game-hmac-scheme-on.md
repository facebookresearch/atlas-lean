# HMAC forgery experiment for forgers with arbitrary coins

Let the chaining values `S` have decidable equality and
the messages `X` have decidable equality, with an encoding `enc : X → List
Bool`. For a forger `A` with arbitrary coins, the forgery experiment
`Mac-forge` of the HMAC scheme on `enc` (Katz and Lindell, Definition 4.2)
draws `r ← A.coins` and then runs the PRF forgery experiment of `k, x ↦
HMAC_k(enc x)`, with a uniform key, for the forger fixed at the coins `r`.
