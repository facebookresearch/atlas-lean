# Zero-knowledge proof of graph isomorphism

The zero-knowledge proof of Goldreich, Micali and Wigderson (J. ACM 1991, Protocol 2 and Theorem 2)
that two graphs $G_0$ and $G_1$ on a common vertex set are isomorphic. The prover knows an isomorphism
$\varphi$ with $G_1 = \varphi(G_0)$. In each round it sends a random relabelling $H = \pi(G_1)$; the
verifier sends a uniform bit $\alpha$; the prover answers $\pi$ if $\alpha = 1$ and $\pi \circ \varphi$
if $\alpha = 0$; the verifier checks that the answer maps $G_\alpha$ onto $H$. If the graphs are not
isomorphic, $H$ cannot be isomorphic to both, so a cheating prover fails each round with probability
at least $\tfrac12$.

Here one round is a Sigma protocol on simple graphs, with the general tools of
[zero-knowledge proofs](../zero-knowledge-proofs/README.md): completeness, special soundness,
soundness error $\tfrac12$ per round and $2^{-m}$ over $m$ rounds against adaptive cheating provers,
perfect honest-verifier zero knowledge, and, against an arbitrary verifier in one round, a rewinding
simulator whose $k$ attempts reproduce every test of the verifier's view within $2^{-k}$.
Goldreich, Micali and Wigderson also compose the simulation over $m$ rounds into the perfect
simulator in expected polynomial time of their Theorem 2.

- [The graph a challenge asks about](pick-graph.md)
- [The graph-isomorphism protocol as a Sigma protocol](sigma.md)
- [Composing relabellings](map-map-perm.md)
- [Relabelling by the identity](map-one-perm.md)
- [Witnesses are isomorphisms](exists-rel-iff-nonempty-iso.md)
- [Non-isomorphic graphs have no witness](forall-not-rel-of-is-empty.md)
- [Completeness of the graph-isomorphism protocol](sigma-complete.md)
- [The extractor](extract.md)
- [Two answers give an isomorphism](map-inv-mul-eq.md)
- [Special soundness of the graph-isomorphism protocol](sigma-special-sound.md)
- [Soundness error $1/2$ per round](win-prob-cheat-game-le-half.md)
- [Soundness error $2^{-m}$ over $m$ rounds](win-prob-seq-cheat-game-le.md)
- [The per-challenge simulator](sim-at.md)
- [Perfect special honest-verifier zero knowledge of the graph-isomorphism protocol](sigma-special-hvzk.md)
- [Perfect honest-verifier zero knowledge of the graph-isomorphism protocol](sigma-hvzk.md)
- [One rewinding attempt for the graph-isomorphism protocol](win-prob-attempt-dist-half.md)
- [Zero knowledge of the graph-isomorphism protocol against an arbitrary verifier, one round](abs-win-prob-simulator-k-sub-le-half-pow.md)

## The Sigma protocol on adjacency functions

A variant of the simple-graph protocol above, on **every** Boolean adjacency function $G : \{0, \dots, n-1\}^2 \to \mathrm{Bool}$, with no symmetry or loop restriction, so directed graphs and graphs with loops are included; simple graphs are the symmetric, irreflexive adjacency functions. A permutation $\sigma$ relabels $G$ to $\sigma \cdot G$ with $(\sigma \cdot G)(u, v) = G(\sigma^{-1} u, \sigma^{-1} v)$, and this is an action of the permutation group. With coins $\rho$ the prover commits to $\rho \cdot G_0$ and answers the challenge bit by $\rho^{-1}$ or $\varphi\rho^{-1}$; only completeness is proved for this variant. The simple-graph relabeling results listed above concern a different domain.

- [Relabelling a graph by a permutation](graph-act.md)
- [Relabeling an adjacency function by a product of permutations](graph-act-mul.md)
- [Relabeling an adjacency function by the identity permutation](graph-act-one.md)
- [The graph-isomorphism Sigma protocol on Boolean adjacency functions](sigma-2.md)
- [Completeness of the Sigma protocol on Boolean adjacency functions](sigma-complete-2.md)

## Related topics

- [Zero-knowledge proofs](../zero-knowledge-proofs/README.md): the Sigma-protocol framework,
  sequential repetition and the rewinding simulator.
- [Zero-knowledge proof of quadratic residuosity](../zero-knowledge-proof-of-quadratic-residuosity/README.md):
  the earlier protocol of Goldwasser, Micali and Rackoff, of the same shape.
- [Graph isomorphism and Arthur–Merlin proofs](../../../../TheoryOfComputation/randomized-and-quantum-complexity/graph-isomorphism-and-arthur-merlin-proofs/README.md):
  the complexity of graph isomorphism; graph non-isomorphism has a two-message private-coin
  interactive proof (Goldreich, Micali and Wigderson, Theorem 1), hence lies in $\mathsf{AM}$.
