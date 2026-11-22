# Textbook RSA encryption under a public key

For a public key consisting of a modulus $n$ and an exponent $e$, encryption is the map
$\mathbb{Z}/n\mathbb{Z} \to \mathbb{Z}/n\mathbb{Z}$, $m \mapsto m^e$. Unlike [RSA encryption](encrypt.md)
for a full key with modulus $n = pq$, it needs only the public key.

## Sources

- J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, Section 11.5.1.
