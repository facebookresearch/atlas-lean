# ElGamal is not CCA secure

Multiplicative ElGamal is not CCA secure: given a challenge $(v, e)$ encrypting $m_b$, the adversary queries the decryption of $(v, e \cdot z)$ for a fixed $z \ne 1$, which is a different ciphertext, obtains $m_b z$, and recovers $b$ with advantage $1$. The same holds for every public-key scheme admitting an efficient ciphertext transformation whose decryption reveals the challenge bit.

## Proof sketch

Use the homomorphism with an encryption of $z$ under randomness $0$; the modified ciphertext differs from the challenge because $z \ne 1$.

## Depends on

- [Public-key CCA experiment](../../security-games/generic-security-games/pub-cca-game.md)

## Proof depends on

- [Multiplicative homomorphism of ElGamal](elgamal-homomorphism.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
