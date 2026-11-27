# Recognizing authorized coalitions with a secret-sharing scheme

Let $\mathcal{A}$ be a monotone access structure on a finite set $\mathcal{P}$ of parties, that is, an upward-closed family of subsets of $\mathcal{P}$ (the authorized coalitions). A secret-sharing scheme for $\mathcal{A}$ with finite nonempty secret space $Z$ draws randomness $\rho$ from a fixed distribution and gives each party $P$ the share $\sigma_P = \mathrm{share}_P(z, \rho)$. It is *perfectly correct* if every authorized coalition $S$ has a reconstruction map that returns $z$ from $(\sigma_P)_{P \in S}$ for every $z$ and $\rho$, and *perfectly private* if for every unauthorized coalition $S$ the distribution of $(\sigma_P)_{P \in S}$ is the same for all secrets. For such a scheme, the *recognition test* for a coalition $S$ draws a uniform secret $z$ and the randomness, computes shares, and accepts iff the reconstruction of $S$ (or any deterministic guess from its view) returns $z$. Then the test accepts every authorized coalition with probability $1$ and every unauthorized coalition with probability exactly $1/|Z|$ for a fixed reconstruction map (at most $1/|Z|$ for any deterministic guesser). In particular the test accepts with probability $1$ if and only if the coalition is authorized (for $|Z| \ge 2$).

## Proof sketch

For unauthorized $S$ the view is independent of the uniform secret, so any function of the view equals it with probability $1/|Z|$.

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
