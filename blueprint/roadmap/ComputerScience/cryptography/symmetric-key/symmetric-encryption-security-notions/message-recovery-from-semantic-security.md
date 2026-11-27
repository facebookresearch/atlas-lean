# Semantic security implies security against message recovery

Let a cipher have message space $\{0,1\}^{L}$ and be one-time semantically secure. Then every efficient adversary, given the encryption of a uniform message $m$, outputs $m$ with probability at most $2^{-L} + \mathrm{SSadv}$ for a semantic-security adversary whose running time exceeds that of the recovery adversary by at most the time of sampling two uniform $L$-bit messages and comparing two $L$-bit strings. The hypothesis that all messages have the same length is necessary: for $M = \{0, 00\}$ and the identity cipher every admissible pair is trivial while message recovery succeeds with probability $1/2$ more than guessing.

## Proof sketch

The semantic-security adversary submits two independent uniform messages, runs the recovery adversary on the challenge, and outputs $1$ iff it recovers $m_1$. In the experiment with $m_0$ the recovery adversary sees an encryption independent of $m_1$, so it outputs $m_1$ with probability $2^{-L}$.

## Depends on

- [Semantic security with error $\varepsilon$](../../security-games/semantic-security-and-indistinguishability/semantically-secure.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
