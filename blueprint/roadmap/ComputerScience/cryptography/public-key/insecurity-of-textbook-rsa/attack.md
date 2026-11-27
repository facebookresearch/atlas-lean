# Eavesdropping attack on textbook RSA

The attack submits the units $m_0 = 1$ and $m_1 = -1$, encrypts $-1$ itself under the public key, and
guesses the challenge bit $1$ (that $m_1 = -1$ was encrypted) exactly when the challenge ciphertext
equals that encryption (Katz and Lindell, Section 11.2.1).
