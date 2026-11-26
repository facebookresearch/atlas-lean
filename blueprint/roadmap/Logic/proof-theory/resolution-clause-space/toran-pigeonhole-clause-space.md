# Torán: the pigeonhole formula needs clause space exactly $n + 2$

For all $m > n \ge 1$, the minimum clause space of a resolution refutation of $\mathrm{PHP}^m_n$ is exactly $n + 2$, independently of the number of pigeons $m$.

## Proof sketch

Upper bound: an explicit refutation processes one hole at a time keeping $n$ partially resolved pigeon clauses plus two working clauses. Lower bound: a configuration of at most $n + 1$ clauses implied by the formula can always be satisfied by a partial matching, which a game argument maintains throughout the refutation.

## Depends on

- [Pigeonhole formulas $\mathrm{PHP}^m_n$](../resolution-lower-bounds/pigeonhole-formulas.md)
- [Clause space of resolution refutations](clause-space-of-resolution.md)

## Sources

- J. Torán, "Space and Width in Propositional Resolution", Bulletin of the EATCS 83, 86–104, 2004.
- M. Alekhnovich, E. Ben-Sasson, A. A. Razborov and A. Wigderson, "Space Complexity in Propositional Calculus", SIAM Journal on Computing 31(4), 1184–1211, 2002.
