# Perfect honest-verifier zero knowledge of the graph-isomorphism protocol

For isomorphic graphs on a finite vertex type, the transcripts of the
[graph-isomorphism protocol](sigma.md) with uniform prover coins and the honest verifier (uniform
challenge) have exactly the distribution of the simulator that draws a uniform
challenge $\alpha$ and a uniform permutation $\sigma$ and outputs $(\sigma(G_\alpha), \alpha, \sigma)$.
This is perfect zero knowledge with respect to the honest verifier only; Goldreich, Micali and
Wigderson's Theorem 2 proves perfect zero knowledge against every expected polynomial-time verifier.
A truncated, one-round form of that statement is
[zero knowledge of the graph-isomorphism protocol against an arbitrary verifier](abs-win-prob-simulator-k-sub-le-half-pow.md).

## Informally uses

- [Perfect special honest-verifier zero knowledge of the graph-isomorphism protocol](sigma-special-hvzk.md)

## Sources

- O. Goldreich, S. Micali and A. Wigderson, "Proofs that yield nothing but their validity or all languages in NP have zero-knowledge proof systems", J. ACM 38 (1991), 691-729, Theorem 2 and Definitions 3 and 5 (zero knowledge, from S. Goldwasser, S. Micali and C. Rackoff, "The knowledge complexity of interactive proof systems", SIAM J. Comput. 18 (1989), 186-208).
