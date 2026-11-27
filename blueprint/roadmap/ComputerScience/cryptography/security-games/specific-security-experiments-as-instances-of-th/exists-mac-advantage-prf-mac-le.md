# The PRF-MAC bound for arbitrary coins

Let the key space `K` be finite and nonempty and the messages `M` have
decidable equality; the forger's coins are arbitrary. Let `M` and `T` be finite,
`T` nonempty with decidable equality, and `F : K → M → T`. For every MAC
forger `A` (with arbitrary coins) there are coins `r` in the support of
`A.coins` such that the forgery advantage of `A` against `prfMac F` is at most
the PRF advantage against `F` of the deterministic distinguisher `macReduction
[] (A.forge r)`, plus `1 / |T|` (Katz and Lindell, Theorem 4.6, with coin
fixing).
