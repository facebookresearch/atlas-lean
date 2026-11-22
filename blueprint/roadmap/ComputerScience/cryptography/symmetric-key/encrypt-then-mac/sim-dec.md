# Simulated decryption oracle

The simulated decryption oracle of Katz and Lindell's reduction (Section 4.5) answers $\bot$ on the
challenge ciphertext. On any other ciphertext it answers the message recorded when the encryption
oracle returned that ciphertext, and $\bot$ if the encryption oracle never returned it.
