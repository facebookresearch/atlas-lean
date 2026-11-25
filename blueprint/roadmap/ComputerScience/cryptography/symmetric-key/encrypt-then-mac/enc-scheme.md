# Encrypt-then-MAC has explicit randomness

For an encryption scheme with explicit randomness $E$, drawn from $\rho$, and a deterministic MAC
$F$, encrypt-then-authenticate encrypts $m$ under $(k_1, k_2)$ as the encrypt-then-MAC ciphertext of
$m$ on randomness $r$, for $r$ drawn from $\rho$. So it has explicit randomness too.
