# Zero-knowledge proofs

Interactive proofs (Goldwasser, Micali and Rackoff, SIAM J. Comput. 1989) let a prover convince
a probabilistic polynomial-time verifier of a statement, with *completeness* (true statements are
accepted) and *soundness* (false statements are rejected with high probability, whatever the prover
does). A proof is *zero knowledge* if everything the verifier sees can be produced by a simulator that
knows only that the statement is true.

This topic holds the general tools, for Sigma protocols (three-move public-coin protocols with a
uniform challenge): completeness, special soundness, the
soundness error $1/\lvert \mathrm{Ch} \rvert$ of one round and $1/\lvert \mathrm{Ch} \rvert^m$ of $m$
sequential rounds against adaptive cheating provers, honest-verifier zero knowledge, and the rewinding
simulator of Goldwasser, Micali and Rackoff for an arbitrary (cheating) verifier in one round: each
attempt succeeds with probability exactly $1/\lvert \mathrm{Ch} \rvert$ and a successful attempt
reproduces the real view exactly, so with $k$ attempts every test of the view has probabilities within
$(1 - 1/\lvert \mathrm{Ch} \rvert)^k$. The protocols themselves (graph isomorphism, quadratic
residuosity, Schnorr) are in their own topics or in the last section. Goldwasser, Micali and Rackoff
also compose the simulation over $m$ rounds and simulate perfectly in expected polynomial time; the
class of languages with interactive proofs appears in $\mathsf{IP} = \mathsf{PSPACE}$, linked below.

## Sigma protocols

- [A Sigma protocol](sigma-protocol.md)
- [Completeness of a Sigma protocol](complete.md)
- [Special soundness of a Sigma protocol](special-sound.md)
- [A witness from two accepting transcripts](exists-witness-of-verify-of-verify.md)
- [The honest transcript](honest-transcript.md)
- [The distribution of honest transcripts](transcript.md)
- [Honest transcripts are accepted](verify-of-mem-support-transcript.md)
- [Perfect honest-verifier zero knowledge](hvzk.md)
- [Statistical honest-verifier zero knowledge](stat-hvzk.md)
- [Perfect HVZK is statistical HVZK with error $0$](stat-hvzk-zero.md)
- [The honest transcript for a fixed challenge](challenge-transcript.md)
- [Perfect special honest-verifier zero knowledge](special-hvzk.md)
- [The uniform-challenge simulator](uniform-challenge-sim.md)
- [Special HVZK implies HVZK](special-hvzk-implies-hvzk.md)
- [Simulated transcripts are accepted](verify-of-mem-support-sim.md)
- [The experiment of a cheating prover](cheat-game.md)
- [Soundness error for false statements](win-prob-cheat-game-le.md)

## Sequential repetition

- [Acceptance of $m$ sequential rounds](all-accept.md)
- [At most one accepted challenge sequence](all-accept-subsingleton.md)
- [The experiment of an adaptive cheating prover over $m$ sequential rounds](seq-cheat-game.md)
- [Soundness error of sequential repetition](soundness-error-of-sequential-repetition.md)

## Simulating an arbitrary verifier by rewinding

- [The view of an arbitrary verifier in one round](real-view-dist.md)
- [One rewinding attempt](attempt-dist.md)
- [One rewinding attempt simulates the real view](win-prob-attempt-dist.md)
- [The rewinding simulator truncated after $k$ attempts](simulator-k.md)
- [The truncated rewinding simulator reproduces the real view](win-prob-simulator-k.md)
- [Zero knowledge against an arbitrary verifier, one round](abs-win-prob-simulator-k-sub-le.md)

## Schnorr identification as a Sigma protocol

- [The Schnorr identification protocol as a Sigma protocol](schnorr-sigma-protocol.md)
- [The Schnorr Sigma-protocol verifier](schnorr-sigma-verify.md)
- [Completeness of Schnorr as a Sigma protocol](schnorr-sigma-complete.md)
- [The Schnorr extractor](schnorr-sigma-extract.md)
- [Special soundness of Schnorr as a Sigma protocol](schnorr-sigma-special-sound.md)
- [Honest Schnorr transcripts](schnorr-sigma-transcript.md)
- [Perfect honest-verifier zero knowledge of Schnorr as a Sigma protocol](schnorr-sigma-hvzk.md)
- [The per-challenge Schnorr simulator](schnorr-sigma-sim-at.md)
- [Perfect special honest-verifier zero knowledge of Schnorr as a Sigma protocol](schnorr-sigma-special-hvzk.md)

## Related topics

- [Zero-knowledge proof of graph isomorphism](../zero-knowledge-proof-of-graph-isomorphism/README.md):
  the protocol of Goldreich, Micali and Wigderson, built on these tools.
- [Zero-knowledge proof of quadratic residuosity](../zero-knowledge-proof-of-quadratic-residuosity/README.md):
  the first zero-knowledge proof (Goldwasser, Micali and Rackoff), built on these tools.
- [Schnorr identification scheme](../schnorr-identification-scheme/README.md): the scheme whose
  Sigma-protocol form is in the last section.
- [Goldwasser–Sipser theorem](../../../../TheoryOfComputation/randomized-and-quantum-complexity/goldwasser-sipser-theorem/README.md):
  private coins add no power to interactive proofs.
- [IP = PSPACE (Shamir)](../../../../TheoryOfComputation/randomized-and-quantum-complexity/ip-eq-pspace.md): the
  power of interactive proofs with polynomially many rounds.
- [Semantic security and indistinguishability](../../security-games/semantic-security-and-indistinguishability/README.md):
  semantic security compares an adversary with a simulator that sees no ciphertext, the same
  simulation paradigm as zero knowledge.
