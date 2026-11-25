# Embedding a coin-based forger preserves the forgery experiment

For messages `M` with decidable equality, a MAC scheme `S` and a forger `A`
with explicit coins, the monadic forgery experiment of `MMACForger.ofCoins A`
against `S` equals the forgery experiment of `A` against `S`.
