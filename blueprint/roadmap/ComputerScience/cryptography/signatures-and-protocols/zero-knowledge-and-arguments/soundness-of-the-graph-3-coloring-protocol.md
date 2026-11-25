# Soundness of the graph 3-coloring protocol

Consider the Goldreich–Micali–Wigderson protocol for graph 3-coloring on a graph $G = (V, E)$ with $|E| \ge 1$. In each round the prover chooses a uniformly random permutation of the three colors, applies it to its coloring and commits to the color of every vertex; the verifier picks a uniformly random edge; the prover opens the commitments at its two endpoints; and the verifier accepts the round if the opened values are two distinct valid colors. The honest prover holding a proper 3-coloring always convinces the verifier. With a perfectly binding commitment scheme, if $G$ is not 3-colorable then the verifier rejects each round with probability at least $1/|E|$, so after $k|E|$ sequential repetitions the soundness error is at most $(1 - 1/|E|)^{k|E|} \le e^{-k}$. With a statistically binding scheme whose binding error per round is at most $\beta$, a union bound over the $k|E|$ rounds gives soundness error at most $e^{-k} + k|E|\beta$.

## Depends on

- [Interactive arguments](interactive-arguments.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- Perfectly and statistically binding commitment definitions (statement prerequisite; not yet stated)

## Sources

- O. Goldreich, S. Micali and A. Wigderson, "Proofs that yield nothing but their validity or all languages in NP have zero-knowledge proof systems", *Journal of the ACM* 38(3):690–728, 1991
