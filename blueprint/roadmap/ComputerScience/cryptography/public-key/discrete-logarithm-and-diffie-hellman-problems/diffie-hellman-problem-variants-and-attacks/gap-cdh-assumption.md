# Gap computational Diffie–Hellman assumption

The *gap-CDH* assumption for a prime-order group family states that every probabilistic polynomial-time adversary, given $(g, g^{\alpha}, g^{\beta})$ and oracle access to a DDH oracle that decides whether a queried triple $(g^{x}, g^{y}, g^{z})$ satisfies $z = xy$, outputs $g^{\alpha\beta}$ with negligible probability.

## Depends on

- [Computational Diffie–Hellman experiment](../../hardness-assumptions/cdh-game.md)
- [Real DDH experiment](../../elgamal-encryption/ddh-real.md)

## Sources

- T. Okamoto and D. Pointcheval, "The Gap-Problems: A New Class of Problems for the Security of Cryptographic Schemes", Public Key Cryptography (PKC 2001), LNCS 1992, 2001.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
