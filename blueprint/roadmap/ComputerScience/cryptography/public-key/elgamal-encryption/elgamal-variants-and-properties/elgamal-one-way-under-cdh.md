# ElGamal is one-way under CDH

Multiplicative ElGamal over a prime-order group family is one-way if CDH holds: an adversary recovering a uniform message from $(g^{\beta}, u^{\beta} m)$ yields a CDH solver.

## Proof sketch

Given a CDH instance $(g^\alpha, g^\beta)$, publish $u = g^\alpha$ and the ciphertext $(g^\beta, z)$ for a uniform $z$; since $m = z / u^{\beta}$ is uniform, recovering $m$ gives $u^\beta = z/m$.

## Depends on

- [One-way and unpredictable public-key encryption](one-way-and-unpredictable-pke.md)
- [Computational Diffie–Hellman experiment](../../hardness-assumptions/cdh-game.md)

## Sources

- D. Pointcheval, "Chosen-Ciphertext Security for Any One-Way Cryptosystem", Public Key Cryptography (PKC 2000), LNCS 1751, 2000, Section 2.1.
- A. Menezes, P. van Oorschot and S. Vanstone, "Handbook of Applied Cryptography", CRC Press, 1996, Note 8.23.
