# RSA-CRT decryption with the standard exponents

Let $(p, q, e, d)$ be an RSA key with
modulus $n = pq$ in which both primes are odd, that is $p > 2$ and $q > 2$. Then for every
$c \in \mathbb{Z}/n\mathbb{Z}$, RSA-CRT decryption of $c$ with the exponents
$d_p = d \bmod (p - 1)$ and $d_q = d \bmod (q - 1)$ equals the RSA decryption $c^d$.
