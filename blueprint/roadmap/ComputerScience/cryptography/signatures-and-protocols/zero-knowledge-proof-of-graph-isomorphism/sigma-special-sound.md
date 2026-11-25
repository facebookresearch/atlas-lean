# Special soundness of the graph-isomorphism protocol

The [graph-isomorphism protocol](sigma.md) is specially sound with the [extractor](extract.md): from
two accepting transcripts with the same commitment $H$ and different challenges, the extractor
computes a permutation mapping $G_0$ onto $G_1$.

## Informally uses

- [Two answers give an isomorphism](map-inv-mul-eq.md)

## Sources

- O. Goldreich, S. Micali and A. Wigderson, "Proofs that yield nothing but their validity or all languages in NP have zero-knowledge proof systems", J. ACM 38 (1991), 691-729, proof of Theorem 2 ("the graphs $H$ sent by him cannot be isomorphic to both $G_1$ and
  $G_0$").
- I. Damgård, *On Σ-protocols*, lecture notes, Aarhus University, 2010 (the notion of special soundness).
