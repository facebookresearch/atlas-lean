# At most a quarter of the bases are non-witnesses

Let $n > 1$ be odd and not prime. Then
at most $\lfloor (n - 1)/4 \rfloor$ of the bases $1, \dots, n - 1$ are non-witnesses for $n$, so one uniformly
random base fails to expose $n$ as composite with probability at most $1/4$.

For odd $n$ this is Rabin's bound: his Theorem 1, stated for his gcd-based witnesses $W_n(b)$, says that at least $3(n - 1)/4$ of the $1 \le b < n$ are witnesses and
covers every composite $n > 4$, even $n$ included, and the Proposition in his note added on
10 May 1978 restates it for odd $n$ with the witnesses found by this test; see
[Rabin's 1/4 bound for strong pseudoprimes](card-is-strong-pseudoprime-le-quarter.md) for the
comparison.

## Sources

- M. O. Rabin, *Probabilistic algorithm for testing primality*, Journal of Number Theory 12 (1980), 128–138: Theorem 1 (p. 130) and the Proposition in the note added on 10 May 1978 (p. 137).
- L. Monier, Theoretical Computer Science 12 (1980), 97–108, proved the same bound independently
  (attribution taken from secondary sources; the paper was not consulted).
