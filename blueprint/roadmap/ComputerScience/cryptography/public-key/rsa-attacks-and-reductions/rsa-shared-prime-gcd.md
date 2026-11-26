# RSA moduli sharing a prime are factored by their gcd

If $N_1 = p q_1$ and $N_2 = p q_2$ for primes with $q_1 \ne q_2$, then $\gcd(N_1, N_2) = p$, computable in polynomial time; this factors both moduli. Keys generated from low-entropy seeds that repeat a prime are therefore broken by pairwise gcds.

## Proof sketch

Unique factorization: the common prime factors of $p q_1$ and $p q_2$ are exactly $p$ when $q_1 \ne q_2$ (also when $q_i = p$ is excluded by distinctness of primes in a key).

## Depends on

- [RSA key](../rsa-cryptosystem/key.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
