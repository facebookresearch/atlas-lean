# Key recovery from leaked or related Schnorr signing nonces

Let a Schnorr signature be $(t, z)$ with $t = g^{r}$, challenge $c = H(m, t)$ read in $\mathbb{Z}_q$, and $z = r + c\alpha$. (a) If the nonce $r$ leaks, the key is $\alpha = (z - r)c^{-1}$; for an $m$-bit random-oracle challenge with $2^m \le q$ this fails only when $c = 0$, i.e. with probability at most $2^{-m}$. (b) If two signatures use related nonces $r_1 = a r_0 + b$ with known $a, b$, then $\alpha = (z_1 - a z_0 - b)/(c_1 - a c_0)$ whenever $a c_0 \ne c_1$, computable in polynomial time.

## Proof sketch

Both are linear algebra in $\mathbb{Z}_q$: subtract the known nonce contribution from the response(s) and divide by the nonzero coefficient of $\alpha$.

## Depends on

- [Security of Schnorr signatures in the random oracle model](../../zero-knowledge-and-arguments/security-of-schnorr-signatures-in-the-random.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
