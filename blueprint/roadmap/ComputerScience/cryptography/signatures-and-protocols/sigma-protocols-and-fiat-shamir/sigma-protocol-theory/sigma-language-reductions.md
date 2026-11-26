# Language reductions transfer soundness of Sigma protocols

Let $\Pi'$ be a Sigma protocol for $\mathcal{R}'$, and let $g : Y \to Y'$ be a statement map and $f$ a witness map. The *derived protocol* $\Pi = \Pi' \circ (f, g)$ for $\mathcal{R}$ runs $\Pi'$ on $g(y)$ with witness $f(x, y)$. If $(x, y) \in \mathcal{R}$ implies $(f(x,y), g(y)) \in \mathcal{R}'$ (condition (i)), completeness and special HVZK are inherited; if every $y$ with $g(y)$ in the language of $\mathcal{R}'$ is in the language of $\mathcal{R}$ (condition (ii)), statistical soundness is inherited: if $\Pi'$ accepts false statements with probability at most $\varepsilon$ against every (unbounded) prover, so does $\Pi$. Moreover a special-sound Sigma protocol is sound with error at most $1/|C|$ against every prover, so every derived protocol is sound with error $1/|C|$.

## Proof sketch

A false statement $y$ of $\mathcal{R}$ maps to a false statement $g(y)$ of $\mathcal{R}'$. For special soundness: on a false statement, for each commitment at most one challenge can be answered acceptably, else the extractor would produce a witness.

## Depends on

- [A Sigma protocol](../../zero-knowledge-proofs/sigma-protocol.md)
- [Special soundness of a Sigma protocol](../../zero-knowledge-proofs/special-sound.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
