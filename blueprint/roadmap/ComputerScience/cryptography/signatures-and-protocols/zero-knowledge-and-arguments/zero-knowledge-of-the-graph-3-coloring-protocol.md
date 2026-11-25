# Zero knowledge of the graph 3-coloring protocol

In the Goldreich–Micali–Wigderson protocol for graph 3-coloring on a graph $G = (V, E)$ with $|E| \ge 1$, the prover commits to the colors of a randomly permuted proper 3-coloring, the verifier chooses an edge, and the prover opens the two colors at its endpoints. If the commitment scheme is computationally hiding, the protocol is computational zero knowledge: for every efficient verifier $V^*$ there is an expected polynomial-time simulator that guesses an edge, commits to a coloring that is proper on that edge (and arbitrary elsewhere), and rewinds $V^*$ until $V^*$ asks for the guessed edge; its output is computationally indistinguishable from the view of $V^*$. The simulator works for every $V^*$ with auxiliary input, so the protocol is auxiliary-input zero knowledge, and auxiliary-input zero knowledge is preserved by sequential repetition.

## Proof depends on

- [Soundness of the graph 3-coloring protocol](soundness-of-the-graph-3-coloring-protocol.md)
- [The hybrid step](../../security-games/games-and-advantages/advantage-hybrid-uniform.md)

## Expansion

This page becomes ready once:

- Computational hiding of a commitment scheme: commitments to any two messages are computationally indistinguishable (statement prerequisite; not yet stated)
- Zero-knowledge interactive proofs (statement prerequisite; not yet stated)

## Sources

- O. Goldreich, S. Micali and A. Wigderson, "Proofs that yield nothing but their validity or all languages in NP have zero-knowledge proof systems", *Journal of the ACM* 38(3):690–728, 1991
