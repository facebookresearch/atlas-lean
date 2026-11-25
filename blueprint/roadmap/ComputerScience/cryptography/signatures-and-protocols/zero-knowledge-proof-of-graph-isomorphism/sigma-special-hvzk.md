# Perfect special honest-verifier zero knowledge of the graph-isomorphism protocol

For isomorphic graphs on a finite vertex type, with any witness $\varphi$, and for each challenge
$\alpha$, the honest pair (commitment, answer) of the [graph-isomorphism protocol](sigma.md), with a
uniform permutation $\pi$ as prover coins, has exactly the distribution of the
[per-challenge simulator](sim-at.md). For $\alpha = 1$ the pair is $(\pi(G_1), \pi)$; for $\alpha = 0$ it
is $(\pi(G_1), \pi \circ \varphi) = (\sigma(G_0), \sigma)$ with $\sigma = \pi \circ \varphi$, which is
uniform when $\pi$ is.

## Informally uses

- [Composing relabellings](map-map-perm.md)

## Sources

- O. Goldreich, S. Micali and A. Wigderson, "Proofs that yield nothing but their validity or all languages in NP have zero-knowledge proof systems", J. ACM 38 (1991), 691-729, proof of Theorem 2 (the simulator "constructs the graph $H$ such that it can answer $V^*$ in
  case it were lucky"; here only the honest verifier is simulated, so no rewinding is needed).
- I. Damgård, *On Σ-protocols*, lecture notes, Aarhus University, 2010 (special honest-verifier zero knowledge).
