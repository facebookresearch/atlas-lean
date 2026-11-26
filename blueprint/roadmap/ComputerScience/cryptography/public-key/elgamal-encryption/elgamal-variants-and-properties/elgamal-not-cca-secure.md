# ElGamal is not CCA secure

Multiplicative ElGamal is not CCA secure: given a challenge $(v, e)$ encrypting $m_b$, the adversary queries the decryption of $(v, e \cdot z)$ for a fixed $z \ne 1$, which is a different ciphertext, obtains $m_b z$, and recovers $b$ with advantage $1$.

## Proof sketch

Use the homomorphism with an encryption of $z$ under randomness $0$; the modified ciphertext differs from the challenge because $z \ne 1$.

## Depends on

- [Public-key CCA experiment](../../../security-games/generic-security-games/pub-cca-game.md)

## Proof depends on

- [Multiplicative homomorphism of ElGamal](elgamal-homomorphism.md)

## Sources

- R. Cramer and V. Shoup, "Design and Analysis of Practical Public-Key Encryption Schemes Secure against Adaptive Chosen Ciphertext Attack", SIAM Journal on Computing 33(1), 2003.
