# XOR-hash from a secure PRF is computationally universal

If $F$ is a PRF and $2^{-w}$ is negligible, the XOR-hash is a computational universal hash function, and for an adversary outputting at most $Q$ messages

$$\mathrm{MUHFadv}(H) \le \mathrm{PRFadv}(F) + \frac{Q^2}{2 \cdot 2^w},$$

where the PRF reduction makes at most $Q L$ queries.

## Proof sketch

With a truly random function on tagged blocks, two distinct messages differ in some position $j$, so the XOR of their hashes includes an independent uniform value $F((j, m_j))$; each pair collides with probability $2^{-w}$.

## Depends on

- [XOR-hash from a pseudorandom function](xor-hash.md)

## Proof depends on

- [Computational universal hashing implies multi-query security](single-to-multi-query-universal-hashing.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
