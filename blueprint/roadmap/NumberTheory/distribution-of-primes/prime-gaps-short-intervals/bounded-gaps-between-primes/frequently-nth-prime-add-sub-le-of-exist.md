# Maynard–Tao theorem: bounded gaps between $m + 1$ consecutive primes

Let $p_0 = 2 < p_1 < \cdots$ be the primes, indexed from $0$. For every natural number $m$ there is $B$ with $p_{n+m} - p_n \le B$ for infinitely many $n$, that is

$$\liminf_{n \to \infty} (p_{n+m} - p_n) < \infty .$$

This is the claim in the abstract of Maynard (2015), obtained independently by Tao. The quantitative form is [Maynard's Theorem 1.1](frequently-nth-prime-add-sub-le-cube-mul.md), which implies this statement. For $m = 1$ it is the finiteness of the [liminf of prime gaps](../prime-gaps/prime-gap-liminf.md), first proved by Zhang.

## Informally uses

- [Maynard's Proposition 4.2](../../sieve-methods/gpy-maynard-sieve/infinite-lt-prime-shift-count-of-lt-mayn.md): the reduction to a lower bound for $M_k$.
- [Growth of $M_k$](../../sieve-methods/gpy-maynard-sieve/eventually-log-sub-lt-maynard-m.md): $M_k \to \infty$.
- [Bombieri–Vinogradov theorem](../../primes-in-progressions/bombieri-vinogradov-theorem/bombieri-vinogradov.md): level of distribution $\theta = \tfrac12 - \varepsilon$.
- [Prime-rich translates give short gaps](../../sieve-methods/gpy-maynard-sieve/frequently-nth-prime-add-sub-le-of-infin.md): from primes in translates to gaps between the primes $p_n$.

## Background

- [Maynard–Tao theorem in tuple form](../smooth-gaps-between-primes/maynard-tao-admissible-tuples.md): every long enough admissible tuple has infinitely many translates with $m$ primes.

## Sources

- J. Maynard, "Small gaps between primes", *Ann. of Math.* 181 (2015), 383–413; theorem and display numbers are those of arXiv:1311.4600v3 (28 Oct 2019).
