# Zero knowledge of the graph-isomorphism protocol against an arbitrary verifier, one round

For isomorphic graphs on a finite vertex type, every verifier (with coins in a finite nonempty
type) and every test $T$ of its view, the rewinding simulator with $k$
attempts (which never sees the isomorphism) and the real interaction pass $T$ with probabilities that
differ by at most $2^{-k}$.

## Informally uses

- [Zero knowledge against an arbitrary verifier, one round](../zero-knowledge-proofs/abs-win-prob-simulator-k-sub-le.md)
- [Perfect special honest-verifier zero knowledge of the graph-isomorphism protocol](sigma-special-hvzk.md)

## Sources

- O. Goldreich, S. Micali and A. Wigderson, "Proofs that yield nothing but their validity or all languages in NP have zero-knowledge proof systems", J. ACM 38 (1991), 691-729, Theorem 2 (perfect zero knowledge of the $m$-round protocol; here one round, truncated
  simulator).
