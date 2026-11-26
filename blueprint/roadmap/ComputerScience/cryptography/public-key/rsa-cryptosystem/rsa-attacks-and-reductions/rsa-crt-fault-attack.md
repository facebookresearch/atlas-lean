# Fault attack on RSA-CRT signing

Let $N = pq$ with odd primes, $ed \equiv 1 \pmod{\varphi(N)}$, and let RSA-CRT compute $x_p = h^{d \bmod (p-1)} \bmod p$, $x_q = h^{d \bmod (q-1)} \bmod q$ and recombine $\sigma = x_q + q\,\bigl(q^{-1}(x_p - x_q) \bmod p\bigr)$, which equals $h^d \bmod N$. If a fault corrupts only the mod-$p$ half, so that $x_q \equiv h^d \pmod q$ but $x_p \not\equiv h^d \pmod p$, then the faulty output $\sigma$ satisfies

$$\gcd(\sigma^{e} - h,\ N) = q.$$

## Proof sketch

The recombined $\sigma$ is congruent to $x_q$ modulo $q$, so $\sigma^e \equiv h \pmod q$; modulo $p$ it is congruent to the faulty $x_p$, and since raising to $e$ is a bijection on $\mathbb{Z}_p$, $\sigma^e \not\equiv h \pmod p$.

## Depends on

- [RSA-CRT decryption](../crt-decrypt.md)

## Proof depends on

- [RSA-CRT decryption is correct](../crt-decrypt-eq.md)

## Sources

- D. Boneh, R. A. DeMillo and R. J. Lipton, "On the Importance of Checking Cryptographic Protocols for Faults", Advances in Cryptology (EUROCRYPT 1997), LNCS 1233, 1997.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
