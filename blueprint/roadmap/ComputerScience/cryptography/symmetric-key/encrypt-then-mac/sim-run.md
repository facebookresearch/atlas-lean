# Simulated chosen-ciphertext game on a random tape

On a tape, the simulated game runs a chosen-ciphertext adversary against encrypt-then-MAC. It
answers encryption queries as the real game does, recording each answer with its message, and
answers decryption queries with the simulated decryption oracle. A decryption query $(c, t)$ that
is not the challenge, has a valid tag $t = F(k_2, c)$ and is not in the table is bad, and the index
of the first bad query is recorded. Every query advances the counter and uses up one tape entry.
