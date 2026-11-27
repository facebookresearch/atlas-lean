# Containment-free and domination-free encodings

A map $P$ from messages to subsets of $\{1, \dots, n\}$ is *containment free* if $P(m) \not\subseteq P(m')$ for all distinct $m, m'$ (this implies injectivity). A map $P$ from messages to vectors in $\{0, \dots, d\}^{n}$ is *domination free* if for all distinct $m, m'$ the vector $P(m)$ is not coordinatewise at most $P(m')$. Containment-free maps give one-time signatures from one-way functions by revealing preimages at the positions in $P(m)$; domination-free maps give one-time signatures with hash chains of length $d$ (Winternitz signatures) when the chain function $f$ is one-way on $d$ iterates, that is, for every $j = 1, \dots, d$ no efficient adversary given $f^{(j)}(x)$ for uniform $x$ finds a preimage of it under $f$ with non-negligible probability (in Boneh and Shoup's form of the scheme, whose secret key is expanded from a seed by a PRG and whose public key is hashed, the PRG must also be secure and the hash collision resistant). One-wayness of $f$ alone does not suffice: a one-way function need not be one-way on $d$ iterates, even for $d = 2$.

## Depends on

- [Lamport signing](../sign.md)
- [Signature scheme](../../../security-games/generic-security-games/sig-scheme.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- L. Lamport, "Constructing Digital Signatures from a One-Way Function", Technical Report CSL-98, SRI International, 1979.
