# Encrypt-then-MAC ciphertext on given randomness

For an encryption scheme with explicit randomness $E$ and a deterministic MAC $F$, the
encrypt-then-MAC ciphertext of $m$ under $(k_1, k_2)$ on randomness $r$ is $(c, F(k_2, c))$ with
$c = E(k_1, m, r)$.
