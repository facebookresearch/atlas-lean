# Auxiliary-input computational zero knowledge

An interactive proof $(P, V)$ for a language $L$ with witness relation $R$ is *auxiliary-input zero knowledge* if for every probabilistic polynomial-time verifier $V^*$ there is a probabilistic polynomial-time simulator $S$ such that the ensembles

$$\{\mathrm{view}_{V^*}[P(x, y) \leftrightarrow V^*(x, z)]\}_{x \in L, (x,y) \in R, z} \quad\text{and}\quad \{S(x, z)\}_{x \in L, z}$$

are computationally indistinguishable by distinguishers that also receive $x$ and $z$, for every auxiliary input $z$ of polynomial length. Auxiliary-input zero knowledge is closed under sequential composition.

## Depends on

- [Zero-knowledge interactive proofs](../../zero-knowledge-and-arguments/zero-knowledge-interactive-proofs.md)
- [Computational indistinguishability of distribution ensembles](../../../security-games/computational-indistinguishability-of-ensembles/computational-indistinguishability-of-ensembles.md)

## Sources

- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
- S. Goldwasser, S. Micali and C. Rackoff, "The Knowledge Complexity of Interactive Proof Systems", SIAM Journal on Computing 18(1), 1989.
