# Correctness of textbook RSA

For an RSA key with modulus $n = pq$ and exponents $e$ and $d$, decryption inverts encryption on
every message: $(m^e)^d = m$ for every $m \in \mathbb{Z}/n\mathbb{Z}$, including messages that are
not coprime to $n$.
