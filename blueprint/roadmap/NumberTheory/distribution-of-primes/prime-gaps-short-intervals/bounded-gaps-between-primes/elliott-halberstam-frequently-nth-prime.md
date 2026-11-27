# Three primes in intervals of length 600 under Elliott–Halberstam

Let $p_0 = 2 < p_1 < \cdots$ be the primes, indexed from $0$. If the [Elliott–Halberstam conjecture](elliott-halberstam.md) holds at every level $\theta < 1$, in Polymath8b's dyadic form, then $p_{n+2} - p_n \le 600$ for infinitely many $n$, that is $\liminf_n (p_{n+2} - p_n) \le 600$ (Maynard (2015), Theorem 1.4, second inequality).

Hypothesis. Maynard assumes that the primes have level of distribution $\theta$ for every $\theta < 1$, in the cumulative form (1.3) with $\pi(x; q, a)$. This page uses the dyadic von Mangoldt form already used for [Maynard's bound under Elliott–Halberstam](maynard-elliott-halberstam-upper-bound.md); the two forms are interchangeable by standard partial summation and dyadic decomposition.

## Informally uses

- [$M_{105} > 4$](../../sieve-methods/gpy-maynard-sieve/four-lt-maynard-m-105.md) and [Maynard's Proposition 4.2](../../sieve-methods/gpy-maynard-sieve/infinite-lt-prime-shift-count-of-lt-mayn.md): with $\theta = 1 - \varepsilon$, three primes in infinitely many translates of an admissible $105$-tuple.
- [Prime-rich translates give short gaps](../../sieve-methods/gpy-maynard-sieve/frequently-nth-prime-add-sub-le-of-infin.md): applied with $m = 2$ to a $105$-tuple of diameter $600$.

## Sources

- J. Maynard, "Small gaps between primes", *Ann. of Math.* 181 (2015), 383–413; theorem and display numbers are those of arXiv:1311.4600v3 (28 Oct 2019).
