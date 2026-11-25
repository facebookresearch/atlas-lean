# Embedding a coin-based forger preserves its advantage

For messages `M` with decidable equality, a MAC scheme `S` and a forger `A`
with explicit coins, the monadic forgery advantage of the embedded forger
`MMACForger.ofCoins A` against `S` equals the forgery advantage of `A` against
`S`.
