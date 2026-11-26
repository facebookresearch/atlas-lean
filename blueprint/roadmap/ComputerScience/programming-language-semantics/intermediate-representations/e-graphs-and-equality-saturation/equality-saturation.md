# Equality saturation

Given a term $t$ and a set $R$ of rewrite rules $\ell \to r$ between patterns, *equality saturation* builds an [e-graph](e-graphs.md) representing $t$, then repeatedly applies every rule of $R$ to the e-graph, by e-matching its left-hand side and merging each match with the corresponding instance of its right-hand side, as described with the [e-graph operations](congruence-and-hashcons-invariants-of-e-graphs.md), until no application adds an e-node or merges two e-classes (the e-graph is *saturated*) or a limit is reached. Finally *extraction* selects, from the e-class of $t$, a represented term of least cost for a given cost function. Applications are additive: no e-node is removed, so every term represented at some point remains represented, and terms represented by one e-class are equal modulo the equations $\ell = r$ of $R$.

## Depends on

- [E-graphs](e-graphs.md)
- [Congruence and hashcons invariants of e-graphs](congruence-and-hashcons-invariants-of-e-graphs.md)

## Sources

- M. Willsey, C. Nandi, Y. R. Wang, O. Flatt, Z. Tatlock and P. Panchekha, "egg: Fast and extensible equality saturation", *Proceedings of the ACM on Programming Languages* 5(POPL):23, 2021, <https://arxiv.org/abs/2004.03082>, Section 2.1.3 (applying rewrites, saturation) and Section 2.2 (the equality saturation workflow, Figure 3, extraction).
- R. Tate, M. Stepp, Z. Tatlock and S. Lerner, "Equality saturation: a new approach to optimization", *POPL 2009*, ACM, 2009, cited by Willsey et al. as the origin of equality saturation.
