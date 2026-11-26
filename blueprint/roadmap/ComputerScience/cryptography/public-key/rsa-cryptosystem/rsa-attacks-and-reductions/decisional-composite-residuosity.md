# Decisional composite residuosity (DCR) assumption

Let $N = pq$ be a product of distinct odd primes of the same bit length. An element of $\mathbb{Z}_{N^2}^*$ is an *$N$-th residue* if it equals $r^{N}$ for some unit $r$. The *DCR assumption* relative to a modulus distribution states that every efficient distinguisher, given $N$, has negligible advantage in distinguishing a uniform $N$-th residue modulo $N^2$ from a uniform unit modulo $N^2$.

## Depends on

- [The residuosity experiment](../../goldwasser-micali-encryption/qr-exp.md)
- [Factoring experiment](../../hardness-assumptions/factor-game.md)

## Sources

- P. Paillier, "Public-Key Cryptosystems Based on Composite Degree Residuosity Classes", Advances in Cryptology (EUROCRYPT 1999), LNCS 1592, 1999.
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd edition, CRC Press, 2020.
