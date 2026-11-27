# ElGamal is not CCA secure

Multiplicative ElGamal is not CCA secure: the adversary submits two distinct messages $m_0 \ne m_1$; given a challenge $(v, e)$ encrypting $m_b$, it queries the decryption of $(v, e \cdot z)$ for a fixed $z \ne 1$, which is a different ciphertext, obtains $m_b z$, and recovers $b$ with probability $1$. Its CCA advantage is therefore $1/2$ in the guessing normalisation $|\Pr[\text{guess} = b] - 1/2|$ of the linked experiment and of Cramer and Shoup (Section 3.2), and $1$ in the distinguishing normalisation, which is twice the guessing one (Section 3.3).

## Proof sketch

Use the homomorphism with an encryption of $z$ under randomness $0$; the modified ciphertext differs from the challenge because $z \ne 1$.

## Depends on

- [Public-key CCA experiment](../../../security-games/generic-security-games/pub-cca-game.md)

## Proof depends on

- [Multiplicative homomorphism of ElGamal](elgamal-homomorphism.md)

## Sources

- R. Cramer and V. Shoup, "Design and Analysis of Practical Public-Key Encryption Schemes Secure against Adaptive Chosen Ciphertext Attack", SIAM Journal on Computing 33(1), 2003, Sections 3.2 and 3.3 (advantage normalisations) and the attack on basic ElGamal in Section 4.
