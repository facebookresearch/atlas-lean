# Maynard's explicit bound for gaps between $m + 1$ primes

Let $p_0 = 2 < p_1 < \cdots$ be the primes, indexed from $0$. There is an absolute constant $C$ such that for every natural number $m \ge 1$,

$$p_{n+m} - p_n \le C\, m^3 e^{4m} \quad \text{for infinitely many } n,$$

that is $\liminf_n (p_{n+m} - p_n) \ll m^3 e^{4m}$ (Maynard (2015), Theorem 1.1). Maynard notes that Tao proved the same result independently with a slightly weaker bound, and that under Elliott–Halberstam the bound improves to $O(m^3 e^{2m})$.

Proof outline in the source: with $\theta = \tfrac12 - \varepsilon$ and $k \ge C m^2 e^{4m}$, Proposition 4.3(3) gives $\theta M_k / 2 > m$, so by Proposition 4.2 every admissible $k$-tuple has infinitely many translates with $m + 1$ primes; the $k$ primes following $k$ form an admissible tuple of diameter $\ll k \log k$.

## Informally uses

- [Maynard's Proposition 4.2](../../sieve-methods/gpy-maynard-sieve/infinite-lt-prime-shift-count-of-lt-mayn.md) and [growth of $M_k$](../../sieve-methods/gpy-maynard-sieve/eventually-log-sub-lt-maynard-m.md): $m + 1$ primes in translates of long admissible tuples.
- [Bombieri–Vinogradov theorem](../../primes-in-progressions/bombieri-vinogradov-theorem/bombieri-vinogradov.md): the level of distribution.
- [Admissibility needs only the primes up to the size of the set](../../prime-patterns/hardy-littlewood-prime-tuples-conjecture/is-admissible-finset-iff-forall-prime-le.md): the $k$ primes following $k$ are admissible.
- [Prime-rich translates give short gaps](../../sieve-methods/gpy-maynard-sieve/frequently-nth-prime-add-sub-le-of-infin.md): the passage to $p_{n+m} - p_n$.
- [Prime number theorem](../../prime-number-theorem/prime-number-theorem/prime-number-theorem.md): the diameter bound $p_{\pi(k)+k} - p_{\pi(k)+1} \ll k \log k$ (an upper bound of Chebyshev type suffices).

## Sources

- J. Maynard, "Small gaps between primes", *Ann. of Math.* 181 (2015), 383–413; theorem and display numbers are those of arXiv:1311.4600v3 (28 Oct 2019).
