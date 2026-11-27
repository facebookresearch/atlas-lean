# Paillier encryption

With public key $N = pq$ for distinct odd primes $p, q$ of the same bit length (so that $\gcd(N, \varphi(N)) = 1$) and secret key $\varphi(N)$, *Paillier encryption* of $m \in \mathbb{Z}_N$ is $c = (1+N)^{m} r^{N} \bmod N^2$ for a uniform unit $r$. Decryption computes $m = \frac{(c^{\varphi(N)} \bmod N^2) - 1}{N}\cdot \varphi(N)^{-1} \bmod N$, using the isomorphism $\mathbb{Z}_N \times \mathbb{Z}_N^* \cong \mathbb{Z}_{N^2}^*$, $(a, b) \mapsto (1+N)^a b^N$, and $(1+N)^a = 1 + aN \bmod N^2$.

## Depends on

- [Decisional composite residuosity (DCR) assumption](decisional-composite-residuosity.md)
- [Public-key encryption scheme](../../../security-games/generic-security-games/pkescheme.md)

## Sources

- P. Paillier, "Public-Key Cryptosystems Based on Composite Degree Residuosity Classes", Advances in Cryptology (EUROCRYPT 1999), LNCS 1592, 1999.
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd edition, CRC Press, 2020.
