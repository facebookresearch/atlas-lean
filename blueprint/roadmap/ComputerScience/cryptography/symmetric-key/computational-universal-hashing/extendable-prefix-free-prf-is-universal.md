# An extendable prefix-free PRF is a computational universal hash

Let $F$ be an extendable prefix-free PRF on block sequences with $w$-bit outputs, $2^{-w}$ and the reciprocal of the block alphabet size negligible. Then $F$ restricted to sequences of $1$ to $\ell$ blocks is a computational universal hash function, and multi-query secure; for $Q$ messages the advantage is at most $\mathrm{PRFadv}^{\mathrm{pf}}(F) + \binom{Q}{2}/2^w$ plus a negligible term for the choice of the extension block.

## Proof sketch

Append a fresh block (distinct from every block in the list) to each distinct message; the extended messages form a prefix-free set, so a prefix-free distinguisher can query them and test for colliding replies. Against a random function, distinct extended messages collide with probability $2^{-w}$, and a collision of the hash implies a collision of the extended values.

## Depends on

- [Prefix-free pseudorandom function](../pseudorandom-function-constructions/prefix-free-pseudorandom-function.md)
- [Computational universal hash function](computational-universal-hash.md)

## Proof depends on

- [Computational universal hashing implies multi-query security](single-to-multi-query-universal-hashing.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
