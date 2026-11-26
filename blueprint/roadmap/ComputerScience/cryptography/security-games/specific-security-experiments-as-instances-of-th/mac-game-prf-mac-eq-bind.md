# The PRF-MAC forgery experiment for arbitrary coins

Let the key space `K` be finite and nonempty and the messages `M` have
decidable equality; the forger's coins are arbitrary. Let the tags `T` have
decidable equality and `F : K → M → T`. For a forger `A` with arbitrary coins
`A.coins : PMF R`, the forgery experiment of `prfMac F` draws `r ← A.coins`
and then runs the PRF forgery experiment of `F` for the forger fixed at coins
`r`.
