# Circular (key-dependent message) security

A public-key scheme is *(single-key) circularly secure* if every efficient adversary has negligible advantage in distinguishing $(pk, E(pk, sk))$ from $(pk, E(pk, 0^{|sk|}))$, possibly together with a CPA challenge. Circular security does not follow from semantic security in general.

## Depends on

- [Public-key eavesdropping experiment](../../../security-games/generic-security-games/pub-cpa-game.md)

## Sources

- D. Boneh, S. Halevi, M. Hamburg and R. Ostrovsky, "Circular-Secure Encryption from Decision Diffie-Hellman", Advances in Cryptology (CRYPTO 2008), LNCS 5157, 2008.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
