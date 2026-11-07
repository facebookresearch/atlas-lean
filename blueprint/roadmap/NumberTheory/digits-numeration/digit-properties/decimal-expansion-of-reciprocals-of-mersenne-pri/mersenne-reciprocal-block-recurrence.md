# Doubling recurrence for the blocks of $1/(2^p - 1)$

Let $p$ be a natural number such
that $M = 2^p - 1$ is prime, let $L$ be the multiplicative order of $10$ modulo $M$ (the period of
the decimal expansion of $1/M$), and suppose that $p$ divides $L$. Put $\ell = L/p$ and let
$N = (10^L - 1)/M$ be the repeating block of $1/M$, read as an $L$-digit integer with leading
zeros. For $1 \le k \le p$ let $B_k = \lfloor N / 10^{\ell (p - k)} \rfloor \bmod 10^\ell$ be
the $k$-th block of $\ell$ digits of $N$ from the left, and extend the indices to all $j \ge 1$
by $B_j = B_k$ where $k = ((j - 1) \bmod p) + 1$. Let $r$ and $s$ be natural numbers with
$1 \le r \le p - 1$, $10^\ell \equiv 2^r \pmod{M}$ and $rs \equiv 1 \pmod{p}$. Then, as
integers:

(i) for every $k$ with $1 \le k \le p$, $B_{ks+1} = 2B_{(k-1)s+1} - 10^\ell$ if $k = p$,
$B_{ks+1} = 2B_{(k-1)s+1} + 1$ if $k = p - r$, and $B_{ks+1} = 2B_{(k-1)s+1}$ otherwise;

(ii) if $r = 1$, then for every $k$ with $1 \le k \le p$, $B_{k+1} = 2B_k - 10^\ell$ if $k = p$,
$B_{k+1} = 2B_k + 1$ if $k = p - 1$, and $B_{k+1} = 2B_k$ otherwise;

(iii) $B_1 + B_2 + \dots + B_p = 10^\ell - 1$.

## Sources

- Amitabha Tripathi, *A Note on the Decimal Expansion of Reciprocals of Mersenne Primes*, INTEGERS 24 (2024), Article A14, Theorem 1.
