# Two-sided switching lemma against the forgetful sampler

Let $D = \{0,1\}^n$ be the block set, of size $N = 2^n$. Consider an adversary making at most $Q$ forward or inverse queries and no redundant query: it never repeats a query, never makes an inverse query at an earlier forward answer, and never makes a forward query at an earlier inverse answer. It distinguishes a uniform permutation with its inverse from the *forgetful* oracle (which answers every forward and every inverse query with an independent uniform element of $D$) with advantage at most $\binom{Q}{2}/N$.

## Proof sketch

Sample the permutation lazily in both directions. Since no query is redundant, every query is fresh, and the two oracles are identical until a forgetful answer lands on a point already defined on its side (an earlier output for a forward query, an earlier input for an inverse query); conditioned on avoiding those points, it is uniform on the points the lazy permutation may still use. The $i$-th answer does so with probability at most $(i-1)/N$, so the triangular bound gives $\binom{Q}{2}/N$.

## Depends on

- [Strong pseudorandom permutation](strong-pseudorandom-permutation.md)

## Proof depends on

- [Triangular (birthday-type) bound for linearly growing bad sets](../../security-games/identical-until-bad-oracle-handlers/triangular-bad-event-bound.md)
- [The PRP/PRF switching lemma](../../security-games/lazy-sampling-and-the-prp-prf-switching-lemma/switching-lemma.md)

## Sources

- S. Halevi and P. Rogaway, "A Tweakable Enciphering Mode", Advances in Cryptology (CRYPTO 2003), LNCS 2729, Springer, 2003, pp. 482–499; Lemma 6 of the full version ($\pm$prp security $\approx$ $\pm$rnd security: for an adversary making at most $q$ queries, none pointless, a random permutation with its inverse and a pair of oracles returning independent random strings are distinguished with advantage at most $q(q-1)/2^{n+1}$), applied with a single tweak. Its pointless queries are exactly the redundant queries excluded here.
