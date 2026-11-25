# The CPA reduction's simulation of the chosen-ciphertext game

Given a MAC key $k_2$, an optional challenge, a final step and a starting table, the simulation runs
a chosen-ciphertext adversary as a chosen-plaintext adversary. An encryption query $m$ is forwarded
to the encryption oracle, whose answer $c$ is returned as $(c, F(k_2, c))$ and recorded in the table
with $m$. A decryption query is answered by the simulated decryption oracle for the challenge and
the current table, and costs one dummy encryption query, of a fixed message whose answer is ignored,
so that the simulation uses randomness exactly as the chosen-ciphertext game does. When the
adversary stops with output $x$, the simulation outputs the final step applied to $x$ and the
current table.
