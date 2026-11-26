# Recognizing authorized coalitions with a secret-sharing scheme

Let a perfectly correct and perfectly private secret-sharing scheme for $\mathcal{A}$ have a finite nonempty secret space $Z$. The *recognition test* for a coalition $S$ draws a uniform secret $z$ and a key, computes shares, and accepts iff the reconstruction of $S$ (or any deterministic guess from its view) returns $z$. Then the test accepts every authorized coalition with probability $1$ and every unauthorized coalition with probability exactly $1/|Z|$ for a fixed reconstruction map (at most $1/|Z|$ for any deterministic guesser), under every allowed key distribution. In particular the test accepts with probability $1$ if and only if the coalition is authorized (for $|Z| \ge 2$).

## Proof sketch

For unauthorized $S$ the view is independent of the uniform secret, so any function of the view equals it with probability $1/|Z|$.

## Depends on

- [Monotone access structures and secret-sharing schemes](access-structures-and-secret-sharing.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
