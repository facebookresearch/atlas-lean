# Zero knowledge of the quadratic-residuosity protocol against an arbitrary verifier, one round

Let $G$ be a finite commutative group and $s^2 = y$. For every verifier whose bit is any function
of the commitment $u$ and of its coins (in a finite nonempty type),
every test $T$ of its view and every $k$, the
[rewinding simulator with $k$ attempts](../zero-knowledge-proofs/simulator-k.md), which uses
[GMR's simulator](sim-at.md) and never sees $s$, and the real interaction produce views passing $T$
with probabilities that differ by at most $2^{-k}$.

Goldwasser, Micali and Rackoff's Theorem 1 asserts more: perfect zero knowledge of the $m$-round
protocol, with a simulator that repeats attempts until success.

## Informally uses

- [Zero knowledge against an arbitrary verifier, one round](../zero-knowledge-proofs/abs-win-prob-simulator-k-sub-le.md)
- [Perfect special honest-verifier zero knowledge of the quadratic-residuosity protocol](sigma-special-hvzk.md)

## Sources

- S. Goldwasser, S. Micali and C. Rackoff, "The knowledge complexity of interactive proof systems", SIAM J. Comput. 18 (1989), 186-208, Section 5, Theorem 1.
