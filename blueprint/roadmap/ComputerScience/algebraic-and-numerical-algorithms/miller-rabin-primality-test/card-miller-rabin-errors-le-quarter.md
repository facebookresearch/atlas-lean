# Quarter error bound for Miller–Rabin with several bases

Let $n > 1$ be odd and not
prime, and let $s$ be a natural number. Among the $(n - 1)^s$ lists $(b_1, \dots, b_s)$ of bases
with $0 < b_i < n$, at most $\lfloor (n - 1)/4 \rfloor^s$ make the Miller–Rabin test of $n$ with
bases $b_1, \dots, b_s$ answer *prime*.

With uniformly random bases the error probability is therefore at most $4^{-s}$.

Rabin's Theorem 2 states the error bound as *smaller than* $1/2^{2k} = 4^{-k}$ for $k$ random
bases, the strict inequality coming from his strict bound on non-witnesses; the counting bound above
is the non-strict form, for odd $n$.

## Sources

- M. O. Rabin, *Probabilistic algorithm for testing primality*, Journal of Number Theory 12 (1980), 128–138: Theorem 2 (p. 134).
