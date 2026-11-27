# Hellman and rainbow tables for time-memory trade-off inversion

Let $f : X \to X$ with $|X| = N$ and let $R_1, \dots, R_t$ be reduction functions. A *rainbow table* stores, for $m$ starting points $x_0$, only the endpoint $x_t$ of the chain $x_i = R_i(f(x_{i-1}))$, $i = 1, \dots, t$, where the $m$ stored endpoints are pairwise distinct: during precomputation a chain whose endpoint duplicates a stored one is discarded (a *Hellman table* uses a single reduction function per table). To invert $y$, for each $j = t, t-1, \dots, 1$ the online phase computes the chain from column $j$ starting with $R_j(y)$, looks up the endpoint, and on a match regenerates the unique stored chain with that endpoint and checks whether it contains a preimage of $y$. The deterministic costs are: $mt$ evaluations of $f$ for the $m$ stored chains, storage $m$ entries, and online search at most $t(t+1)/2$ evaluations plus at most $t$ chain regenerations of length at most $t$; if $y$ appears as a value $f(x_{i-1})$ in some stored chain, the search returns a preimage.

## Proof sketch

A preimage covered at column $i$ of a stored chain is found when the online chain started at column $i$ reaches that chain's endpoint, which the lookup returns because stored endpoints are distinct; a match whose regenerated chain contains no preimage of $y$ is a false alarm, rejected by the check, and the search moves on. The costs follow by counting chain steps at each starting column, with at most one regeneration per column. Choosing $mt^2 \approx N$ gives Hellman's $T M^2 \approx N^2$ trade-off heuristically.

## Depends on

- [Inversion experiment](../../security-games/asymptotic-security/invert-game.md)

## Sources

- M. E. Hellman, "A Cryptanalytic Time-Memory Trade-Off", IEEE Transactions on Information Theory 26(4), 1980.
- P. Oechslin, "Making a Faster Cryptanalytic Time-Memory Trade-Off", Advances in Cryptology (CRYPTO 2003), LNCS 2729, 2003.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023, Section 18.7 (duplicate endpoints are discarded during preprocessing).
