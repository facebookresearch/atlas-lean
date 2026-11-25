# Completeness of the graph-isomorphism protocol

The [graph-isomorphism protocol](sigma.md) is complete: if $\varphi$ maps $G_0$ onto $G_1$, then for all
prover coins $\pi$ and both challenges the honest answer is accepted. For $\alpha = 1$ the answer $\pi$
maps $G_1$ onto $H = \pi(G_1)$; for $\alpha = 0$ the answer $\pi \circ \varphi$ maps $G_0$ onto
$\pi(\varphi(G_0)) = H$.

## Informally uses

- [Composing relabellings](map-map-perm.md)

## Sources

- O. Goldreich, S. Micali and A. Wigderson, "Proofs that yield nothing but their validity or all languages in NP have zero-knowledge proof systems", J. ACM 38 (1991), 691-729, proof of Theorem 2 ("if the input graphs are isomorphic, then the prover can easily supply
  the permutations required by the verifier").
