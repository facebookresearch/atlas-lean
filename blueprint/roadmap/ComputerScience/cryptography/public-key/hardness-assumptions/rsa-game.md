# RSA-inversion experiment

An RSA key consists of distinct primes $p$ and $q$, the modulus $n = pq$, and exponents $e$ and $d$
with $ed \equiv 1$ modulo $p - 1$ and modulo $q - 1$. For a key-generation distribution on RSA keys,
the RSA-inversion experiment (Katz and Lindell, Section 8.2.4) draws a key, a uniform unit
$y \in (\mathbb{Z}/n)^\times$ and uniform coins, gives the inverter $(n, e, y)$, and outputs $1$ when
its output $x \in \mathbb{Z}/n$ satisfies $x^e = y$.
