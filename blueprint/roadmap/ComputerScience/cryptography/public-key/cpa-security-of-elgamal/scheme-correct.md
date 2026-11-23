# Correctness of ElGamal as a public-key encryption scheme

Let $G$ be a commutative group, $q \ge 1$ a natural number and $g \in G$. As a public-key encryption
scheme, ElGamal generates a key pair by drawing a uniform secret key $x \in \mathbb{Z}/q\mathbb{Z}$ and
publishing $g^x$, encrypts a message $m \in G$ under a public key $h$ by drawing uniform randomness
$y \in \mathbb{Z}/q\mathbb{Z}$ and forming the ElGamal ciphertext, and decrypts with the secret key,
never failing. The scheme is correct: for every key pair in the support of key generation, every
message $m$ and every ciphertext $c$ in the support of the encryption of $m$, decrypting $c$ returns
$m$. This is [the correctness of ElGamal](../elgamal-encryption/decrypt-encrypt.md), restated for the
scheme with randomized key generation and encryption.

## Sources

- J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, Construction 11.16.
