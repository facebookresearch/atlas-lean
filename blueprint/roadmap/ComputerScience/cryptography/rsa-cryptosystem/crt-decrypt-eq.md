# RSA-CRT decryption is correct

Let $(p, q, e, d)$ be an RSA key with modulus $n = pq$, and
let $d_p, d_q \ge 1$ be natural numbers with $d_p \equiv d \pmod{p - 1}$ and
$d_q \equiv d \pmod{q - 1}$. Then for every $c \in \mathbb{Z}/n\mathbb{Z}$, RSA-CRT decryption of
$c$ with the exponents $d_p$ and $d_q$ equals the RSA decryption $c^d$.
