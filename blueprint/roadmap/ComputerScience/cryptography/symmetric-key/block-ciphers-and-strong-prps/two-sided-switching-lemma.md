# Two-sided switching lemma against the forgetful sampler

Let $D$ be a finite block set of size $N$. Consider an adversary making at most $Q$ forward or inverse queries and no redundant query: it never repeats a query, never makes an inverse query at an earlier forward answer, and never makes a forward query at an earlier inverse answer. It distinguishes a uniform permutation with its inverse from the *forgetful* oracle (which answers every forward and every inverse query with an independent uniform element of $D$) with advantage at most $\binom{Q}{2}/N$.

## Proof sketch

Sample the permutation lazily in both directions. Since no query is redundant, every query is fresh, and the two oracles are identical until a forgetful answer lands on a point already defined on its side (an earlier output for a forward query, an earlier input for an inverse query); conditioned on avoiding those points, it is uniform on the points the lazy permutation may still use. The $i$-th answer does so with probability at most $(i-1)/N$, so the triangular bound gives $\binom{Q}{2}/N$.

## Depends on

- [Strong pseudorandom permutation](strong-pseudorandom-permutation.md)

## Proof depends on

- [Triangular (birthday-type) bound for linearly growing bad sets](../../security-games/identical-until-bad-oracle-handlers/triangular-bad-event-bound.md)
- [The PRP/PRF switching lemma](../../security-games/lazy-sampling-and-the-prp-prf-switching-lemma/switching-lemma.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023, the no-redundant-query convention in the proof of Theorem 8.6.
