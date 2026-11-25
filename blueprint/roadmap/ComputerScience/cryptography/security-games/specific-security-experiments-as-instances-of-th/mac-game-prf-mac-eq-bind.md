# The PRF-MAC forgery experiment for arbitrary coins

Let the key space `K` and the forger's coin space `R` be finite and nonempty,
and let the messages `M` have decidable equality. Let the tags `T` have
decidable equality and `F : K → M → T`. For a forger `A` with arbitrary coins
`A.coins : PMF R`, the forgery experiment of `prfMac F` draws `r ← A.coins`
and then runs the PRF forgery experiment of `F` for the forger fixed at coins
`r`.
