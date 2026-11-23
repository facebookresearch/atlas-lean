# The gcd with pq is a prime factor exactly when one prime divides

Let $p \ne q$ be primes and $v$ a natural number. Then $\gcd(v, pq) \in \{p, q\}$ if and only if
exactly one of $p$, $q$ divides $v$.

This is the success test of Rabin's factoring algorithm, $1 < \gcd(k - k_1, n) < n$ for
$n = pq$: for a residue $x$ modulo $pq$ it says that the test succeeds exactly when $x$ vanishes
modulo one prime and not the other.

## Sources

- M. O. Rabin, *Digitalized signatures and public-key functions as intractable as factorization*, MIT/LCS/TR-212, MIT Laboratory for Computer Science, January 1979, Section 4, proof of Theorem 1, equation (6).
