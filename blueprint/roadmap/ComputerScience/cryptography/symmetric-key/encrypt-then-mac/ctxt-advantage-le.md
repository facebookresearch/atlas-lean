# Encrypt-then-MAC has ciphertext integrity

Let the encryption scheme have explicit randomness and the MAC be deterministic with canonical
verification. Every ciphertext forger against encrypt-then-MAC that makes at most $q$ encryption
queries has ciphertext-forgery advantage at most the forgery advantage, against the MAC, of the MAC
forger built from it with a random tape of $q$ samples of the encryption randomness (Katz and
Lindell, Section 4.5). There is no guessing factor: a fresh valid ciphertext is a valid tag on a value
that was never tagged.
