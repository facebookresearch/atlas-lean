# HMAC on bounded-length bit strings is a secure MAC if it is a PRF

Let the chaining values `S` be finite and nonempty with decidable equality and
the coins `R` finite and nonempty. For every forger `A` with arbitrary coins
whose queries and forgery are bit strings shorter than `maxLen` (relabeled
into all bit strings), there are coins `r` in the support of `A.coins` such
that its forgery advantage against HMAC is at most the PRF advantage of the
deterministic distinguisher `macReduction [] (A.forge r)` against HMAC on
messages shorter than `maxLen`, plus `1 / |S|` (Katz and Lindell, Theorem
4.6). The length bound makes the message space finite, as the random-function
experiment requires.
