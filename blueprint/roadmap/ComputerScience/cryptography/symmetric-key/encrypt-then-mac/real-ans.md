# Real oracle answers of encrypt-then-MAC on given randomness

For keys $(k_1, k_2)$ and an optional challenge $c^*$, the real chosen-ciphertext oracles of
encrypt-then-MAC answer an encryption query $m$ on randomness $r$ with the encrypt-then-MAC
ciphertext of $m$ on $r$. They answer a decryption query $(c, t)$ with $\bot$ if it is the challenge
or $t \neq F(k_2, c)$, and with $\mathrm{Dec}_{k_1}(c)$ otherwise; decryption ignores the randomness.
