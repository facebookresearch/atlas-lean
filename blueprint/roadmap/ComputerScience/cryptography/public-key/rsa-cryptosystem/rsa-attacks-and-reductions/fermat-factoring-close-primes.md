# Fermat factoring of RSA moduli with close primes

If $N = pq$ for distinct primes, then $0 < \tfrac{p+q}{2} - \sqrt{N} < \frac{(p-q)^2}{8\sqrt{N}}$. Consequently, if $|p - q| < 2N^{1/4}$ and $p, q$ are odd, then $A = \lceil\sqrt{N}\,\rceil$ equals $(p+q)/2$, and $p, q$ are the roots of $X^2 - 2AX + N$; this factors $N$ in time polynomial in $\log N$.

## Proof sketch

$(p-q)^2 = (p+q)^2 - 4N = (p+q-2\sqrt N)(p+q+2\sqrt N)$ and $p+q+2\sqrt N > 4\sqrt N$, so $0 < p+q-2\sqrt N < \frac{(p-q)^2}{4\sqrt N}$, which is below $1$ when $|p-q| < 2N^{1/4}$. Since $(p+q)/2$ is an integer greater than or equal to $\sqrt N$, it equals $\lceil \sqrt N\rceil$.

## Depends on

- [RSA key](../key.md)
- [Factoring experiment](../../hardness-assumptions/factor-game.md)

## Sources

- B. de Weger, "Cryptanalysis of RSA with Small Prime Difference", Applicable Algebra in Engineering, Communication and Computing 13(1), 2002, Sections 2 and 3.
