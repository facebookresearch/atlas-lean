# Hash-then-PRF composition from a computational universal hash

Let $H$ be a computational universal hash family mapping a variable-length message domain to $\{0,1\}^{w}$, and $F$ a PRF on $w$-bit inputs, with independent keys. Then $F'((k_h, k_f), m) = F(k_f, H(k_h, m))$ is a PRF on the message domain. For an adversary making $Q$ queries,

$$\mathrm{PRFadv}(F') \le \mathrm{PRFadv}(F) + \frac{Q^2}{2}\,\mathrm{UHFadv}(H).$$

## Proof sketch

Replace $F$ by a random function. Then $F'$ differs from a random function on the messages only if two distinct queried messages collide under $H$, which the multi-query universal-hash game bounds.

## Depends on

- [Computational universal hash function](../computational-universal-hashing/computational-universal-hash.md)
- [Asymptotic PRF security relative to a class of distinguishers](../pseudorandom-functions/prfsecure.md)

## Proof depends on

- [Computational universal hashing implies multi-query security](../computational-universal-hashing/single-to-multi-query-universal-hashing.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. N. Wegman and J. L. Carter, "New Hash Functions and Their Use in Authentication and Set Equality", Journal of Computer and System Sciences 22(3), 1981.
