# Soundness error $1/2$ per round

If $G_0$ and $G_1$ are not isomorphic, every cheating prover with coins in a finite type, committing to
a graph and then answering the uniform challenge, is accepted by the verifier of one round of the
[graph-isomorphism protocol](sigma.md) with probability at most $\tfrac12$.

## Informally uses

- [Special soundness of the graph-isomorphism protocol](sigma-special-sound.md)
- [Non-isomorphic graphs have no witness](forall-not-rel-of-is-empty.md)

## Sources

- O. Goldreich, S. Micali and A. Wigderson, "Proofs that yield nothing but their validity or all languages in NP have zero-knowledge proof systems", J. ACM 38 (1991), 691-729, proof of Theorem 2 (the cheating prover cannot answer both challenges for the same
  $H$, so it fails each iteration with probability at least $\tfrac12$).
