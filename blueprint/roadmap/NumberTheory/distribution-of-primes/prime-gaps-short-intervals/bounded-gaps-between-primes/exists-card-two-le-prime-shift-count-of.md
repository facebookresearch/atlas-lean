# GPY: level beyond $\tfrac12$ gives two primes in long admissible tuples

For every $\vartheta > \tfrac12$ there is $k_0$ such that, if the primes have level of distribution $\vartheta$, every admissible set $H$ of at least $k_0$ non-negative integers has infinitely many $n$ with at least two of the $n + h$, $h \in H$, prime (Goldston, Pintz and Yıldırım, Theorem 1, first sentence). The source's constant $C(\vartheta)$ is explicitly calculable; that is not recorded. The conclusion is now known unconditionally: the [Maynard–Tao theorem in tuple form](../smooth-gaps-between-primes/maynard-tao-admissible-tuples.md) with $m = 2$ implies this statement for every $\vartheta$ (up to viewing natural-number shifts as integers and translating $n$). It is kept as GPY's historical conditional result.

Hypothesis. GPY's level of distribution $\vartheta$ is (1.3) for moduli $q \le N^{\vartheta - \varepsilon}$, every $\varepsilon > 0$, with $\theta(N; q, a)$. Here it is the [dyadic Elliott–Halberstam estimate](elliott-halberstam-at.md) at every level $\theta < \vartheta$; the two are interchangeable by standard arguments. Admissibility is [the finite-set notion](../../prime-patterns/hardy-littlewood-prime-tuples-conjecture/is-admissible-finset.md) applied to $H$ viewed in $\mathbb Z$.

## Informally uses

- [GPY detection principle over dyadic ranges](../../sieve-methods/gpy-maynard-sieve/infinite-lt-prime-shift-count-of-eventua.md): GPY show $\sum_n (\sum_i \mathbf 1_{\mathbb P}(n + h_i) - 1) w_n > 0$ for their weights.

## Background

- [Selberg sieve](../../sieve-methods/selberg-sieve/README.md): GPY's weights $\lambda_d = \mu(d)(\log R/d)^{k+\ell}$ modify Selberg's (as described in Maynard, *Small gaps between primes*, Section 2, display (2.3)).

## Sources

- D. A. Goldston, J. Pintz and C. Y. Yıldırım, "Primes in tuples I", *Ann. of Math.* 170 (2009), 819–862; theorem and display numbers are those of arXiv:math/0508185v1 (10 Aug 2005).
