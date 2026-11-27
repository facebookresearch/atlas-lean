# Torán: refuting the pigeonhole formula needs space $n + 1$ for every number of pigeons

For all $m > n \ge 2$, refuting $\mathrm{PHP}^m_n$ needs Esteban–Torán space exactly $n + 1$, independently of the number of pigeons $m$. Consequently its clause space is at least $n + 1$ and at most $n + 2$.

## Proof sketch

Upper bound: Messner showed that $n + 1$ pebbles suffice. Lower bound: take the last stage of a pebbling at which some partial assignment satisfies all pebbled clauses without falsifying an initial clause, chosen of minimal size. The next pebble goes on an initial clause, and every way of satisfying it falsifies some initial clause; for a pigeon clause this forces the assignment to touch every hole, for a hole clause at least $n$ variables, so at least $n$ clauses were pebbled before and $n + 1$ after.

## Depends on

- [Pigeonhole formulas $\mathrm{PHP}^m_n$](../resolution-lower-bounds/pigeonhole-formulas.md)
- [Clause space of resolution refutations](clause-space-of-resolution.md)

## Sources

- J. Torán, "Space and Width in Propositional Resolution", Bulletin of the EATCS 83, 86–104, 2004: Section 4.
- J. L. Esteban and J. Torán, "Space Bounds for Resolution", Information and Computation 171(1), 84–97, 2001: Theorem 21 and the remark after it (Messner's matching upper bound).
- M. Alekhnovich, E. Ben-Sasson, A. A. Razborov and A. Wigderson, "Space Complexity in Propositional Calculus", SIAM Journal on Computing 31(4), 1184–1211, 2002.
