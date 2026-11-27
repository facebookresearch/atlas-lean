# Language reductions transfer completeness and special HVZK of Sigma protocols

Let $R$ and $R'$ be relations, and let $f : X \times Y \to X'$ and $g : Y \to Y'$ satisfy (i) $(f(x, y), g(y)) \in R'$ whenever $(x, y) \in R$, and (ii) $g(y) \in L_{R'}$ implies $y \in L_R$. From a Sigma protocol $P'$ for $R'$ define $P$ for $R$ by running the prover of $P'$ on $(f(x, y), g(y))$ and the verifier on $g(y)$. If $P'$ is complete, so is $P$; if $P'$ is special HVZK with simulator $\mathrm{Sim}'$, then $P$ is special HVZK with the simulator $\mathrm{Sim}'(g(y), c)$.

## Proof sketch

Conversations of $P$ are conversations of $P'$ on the mapped statement, so acceptance and the simulated distribution transfer verbatim; condition (i) supplies valid witnesses for the honest prover.

## Depends on

- [A Sigma protocol](../../zero-knowledge-proofs/sigma-protocol.md)
- [Completeness of a Sigma protocol](../../zero-knowledge-proofs/complete.md)
- [Perfect special honest-verifier zero knowledge](../../zero-knowledge-proofs/special-hvzk.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
