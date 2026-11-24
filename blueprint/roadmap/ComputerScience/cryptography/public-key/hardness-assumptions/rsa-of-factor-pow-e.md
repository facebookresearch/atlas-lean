# Correctness of the reduction from RSA to factoring

Let $(n, e)$ be the public key of an RSA key: distinct primes $p$ and $q$ with $n = pq$, and
exponents $e$ and $d$ with $ed \equiv 1$ modulo $p - 1$ and modulo $q - 1$. Let $F$ be a factoring
algorithm and $s$ its coins. If $F$, on input $n$ with coins $s$, outputs a nontrivial factorization
of $n$, then the RSA inverter built from $F$, run on $(n, e)$, any $y \in \mathbb{Z}/n$ and the same
coins $s$, outputs an $e$-th root of $y$.
