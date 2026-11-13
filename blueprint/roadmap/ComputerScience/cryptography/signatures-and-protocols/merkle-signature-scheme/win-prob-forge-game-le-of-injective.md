# Reduction to Lamport for injective hashes

The key-mismatch event is empty, so the forgery
probability is at most `N` times the success probability of the Lamport forger. This is a complete
reduction to Lamport one-time security, but only for injective hashes, which cannot compress (an
injective `h : A → A → A` needs an infinite or trivial `A`); it says nothing about compressing hash
functions.
