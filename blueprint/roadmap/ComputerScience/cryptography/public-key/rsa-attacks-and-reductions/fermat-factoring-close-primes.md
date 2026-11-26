# Fermat factoring of RSA moduli with close primes

For positive reals $p, q$ with $|p - q| < 2(pq)^{1/4}$, one has $\bigl|\tfrac{p+q}{2} - \sqrt{pq}\bigr| < \tfrac12$. Consequently, if $N = pq$ for distinct odd primes with $|p - q| < 2N^{1/4}$, then $A = \lceil\sqrt{N}\,\rceil$ equals $(p+q)/2$, and $p, q$ are the roots of $X^2 - 2AX + N$; this factors $N$ in time polynomial in $\log N$.

## Proof sketch

$\tfrac{p+q}{2} - \sqrt{pq} = \frac{(p-q)^2}{2(\sqrt p + \sqrt q)^2} < \frac{4\sqrt{pq}}{8\sqrt{pq}} = \tfrac12$, using $(\sqrt p + \sqrt q)^2 \ge 4\sqrt{pq}$. Since $(p+q)/2$ is an integer greater than or equal to $\sqrt N$, it equals $\lceil \sqrt N\rceil$.

## Depends on

- [RSA key](../rsa-cryptosystem/key.md)
- [Factoring experiment](../hardness-assumptions/factor-game.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
