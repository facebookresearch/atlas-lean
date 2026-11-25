# Zero-knowledge proof of quadratic residuosity

The first zero-knowledge proof system (Goldwasser, Micali and Rackoff, Section 5). To prove that $y$
is a quadratic residue modulo $x$ without revealing a square root, the prover sends a random
quadratic residue $u$; the verifier sends a random bit; the prover answers with a square root of $u$
(bit $0$) or of $u y$ (bit $1$); the verifier checks the square; this is repeated $m$ times. A
cheating prover for a non-residue cannot have both $u$ and $u y$ be squares, so it fails each round
with probability at least $\tfrac12$ (Claim 1); and the protocol is perfectly zero knowledge
(Theorem 1).

Here the protocol is stated in any finite commutative group (the units modulo $x$ in the paper), as
a Sigma protocol in the framework of [zero-knowledge proofs](../zero-knowledge-proofs/README.md),
with soundness error $2^{-m}$, perfect special honest-verifier zero knowledge with the paper's
simulator, and, against an arbitrary verifier in one round, a rewinding simulator whose $k$ attempts
reproduce every test of the verifier's view within $2^{-k}$. The paper also composes the simulation
over $m$ rounds, simulates perfectly in expected polynomial time, and gives a proof system for
quadratic non-residuosity (Section 6).

- [The quadratic-residuosity protocol as a Sigma protocol](sigma.md)
- [Completeness of the quadratic-residuosity protocol](sigma-complete.md)
- [The extractor of the quadratic-residuosity protocol](extract.md)
- [Special soundness of the quadratic-residuosity protocol](sigma-special-sound.md)
- [Non-squares have no witness](forall-not-rel-of-not-is-square.md)
- [Soundness error $1/2$ per round](win-prob-cheat-game-le-half.md)
- [Soundness error $2^{-m}$ over $m$ rounds](win-prob-seq-cheat-game-le.md)
- [GMR's per-challenge simulator](sim-at.md)
- [Perfect special honest-verifier zero knowledge of the quadratic-residuosity protocol](sigma-special-hvzk.md)
- [Zero knowledge of the quadratic-residuosity protocol against an arbitrary verifier, one round](abs-win-prob-simulator-k-sub-le-half-pow.md)

## Related topics

- [Zero-knowledge proofs](../zero-knowledge-proofs/README.md): the Sigma-protocol framework, sequential repetition, the
  rewinding simulator, and the graph-isomorphism protocol of Goldreich, Micali and Wigderson.
- [Goldwasser–Micali encryption](../../public-key/goldwasser-micali-encryption/README.md): the same quadratic
  residuosity problem, as the hardness assumption behind probabilistic encryption.
