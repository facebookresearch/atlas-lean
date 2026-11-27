# Re-encryption adversary

Against a deterministic scheme, the re-encryption adversary (Katz and Lindell, Section 11.2.1) submits
a fixed eligible pair $(m_0, m_1)$ for each public key, encrypts $m_1$ itself, and guesses $1$ exactly
when the challenge ciphertext equals that encryption. It uses no coins.
