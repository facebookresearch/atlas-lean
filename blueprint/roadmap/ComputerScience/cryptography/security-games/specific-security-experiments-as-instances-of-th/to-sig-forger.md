# Lamport one-time forger as a signature forger

A Lamport one-time forger `A`, given as a function of its coins, viewed as a
signature forger with uniformly distributed coins: it makes exactly one
signing query, on the message `A.choose pk r`.
