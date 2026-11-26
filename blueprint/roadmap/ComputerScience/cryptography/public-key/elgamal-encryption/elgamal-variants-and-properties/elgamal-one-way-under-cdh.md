# ElGamal is one-way under CDH

Multiplicative ElGamal over a prime-order group family is one-way if CDH holds: an adversary recovering a uniform message from $(g^{\beta}, u^{\beta} m)$ yields a CDH solver with the same success probability.

## Proof sketch

Given a CDH instance $(g^\alpha, g^\beta)$, publish $u = g^\alpha$ and the ciphertext $(g^\beta, z)$ for a uniform $z$; since $m = z / u^{\beta}$ is uniform, recovering $m$ gives $u^\beta = z/m$.

## Depends on

- [One-way and unpredictable public-key encryption](one-way-and-unpredictable-pke.md)
- [Computational Diffie–Hellman experiment](../../hardness-assumptions/cdh-game.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
