# Strong pseudorandom permutation

A block cipher $(E, D)$ is a *strong PRP* (secure against two-sided queries) if every efficient adversary with oracle access to both $E(k, \cdot)$ and $D(k, \cdot)$ for uniform $k$ has negligible advantage in distinguishing them from a uniform permutation $\pi$ and its inverse $\pi^{-1}$.

## Depends on

- [Block cipher (uniform family)](block-cipher.md)

## Sources

- M. Luby and C. Rackoff, "How to Construct Pseudorandom Permutations from Pseudorandom Functions", SIAM Journal on Computing 17(2), 1988.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
