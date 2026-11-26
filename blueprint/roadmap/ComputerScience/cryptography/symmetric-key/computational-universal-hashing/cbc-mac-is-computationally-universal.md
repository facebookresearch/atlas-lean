# CBC-MAC from a secure PRF is computationally universal

If $F$ is a PRF on $n$-bit blocks with $2^{-n}$ negligible, then raw CBC-MAC on messages of $0$ to $\ell(n)$ blocks is a computational universal hash function and multi-query secure, with advantage at most

$$\mathrm{PRFadv}(F) + \frac{Q^2(\ell+1)^2}{2 \cdot 2^n} + \frac{\binom{Q}{2}}{2^n}$$

for an adversary outputting $Q$ messages.

## Proof sketch

CBC-MAC is an extendable prefix-free PRF on messages of up to $\ell+1$ blocks; apply the general prefix-free-PRF universality theorem with the CBC-MAC prefix-free bound.

## Depends on

- [CBC-MAC](../cbc-mac-and-mac-security/cbc-mac.md)
- [Computational universal hash function](computational-universal-hash.md)

## Proof depends on

- [An extendable prefix-free PRF is a computational universal hash](extendable-prefix-free-prf-is-universal.md)
- [CBC-MAC is a prefix-free PRF](../cbc-mac-and-mac-security/cbc-mac-is-a-prefix-free-prf.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
