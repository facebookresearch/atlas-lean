# Forgery experiment for monadic MAC forgers

For messages `M` with decidable equality, a MAC scheme `S` and a monadic
forger `A`, the forgery experiment `Mac-forge` of Katz and Lindell (Definition
4.2): a key is sampled, `A` queries the tagging oracle and outputs a message
and tag, and the experiment returns `true` when the tag verifies on a message
that was not queried.
