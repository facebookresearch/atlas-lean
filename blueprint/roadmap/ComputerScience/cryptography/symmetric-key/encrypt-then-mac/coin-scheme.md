# Encryption with explicit randomness

Given a key distribution $\mathrm{Gen}$, a distribution $\rho$ on randomness, a deterministic function
$E(k, m, r)$ and a decryption algorithm, the scheme with explicit encryption randomness generates its
keys with $\mathrm{Gen}$, encrypts $m$ under $k$ as $E(k, m, r)$ for $r$ drawn from $\rho$, and
decrypts with the given decryption algorithm.
