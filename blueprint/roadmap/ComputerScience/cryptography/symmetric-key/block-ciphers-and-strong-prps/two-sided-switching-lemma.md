# Two-sided switching lemma against the forgetful sampler

Let $D$ be a finite block set of size $N$. An adversary making at most $Q$ forward or inverse queries distinguishes a uniform permutation with its inverse from the *forgetful* oracle (which answers every forward and every inverse query with an independent uniform element of $D$) with advantage at most $\binom{Q}{2}/N$, plus the probability $\binom{Q}{2}/N$ that it asks a query whose answer it could predict, giving $2\binom{Q}{2}/N$ in total.

## Proof sketch

Sample the permutation lazily in both directions. The two oracles are identical until a fresh answer collides with an earlier input or output, which by the triangular bound happens with probability at most $\binom{Q}{2}/N$ per side.

## Depends on

- [Strong pseudorandom permutation](strong-pseudorandom-permutation.md)

## Proof depends on

- [Triangular (birthday-type) bound for linearly growing bad sets](../../security-games/identical-until-bad-oracle-handlers/triangular-bad-event-bound.md)
- [The PRP/PRF switching lemma](../../security-games/lazy-sampling-and-the-prp-prf-switching-lemma/switching-lemma.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
