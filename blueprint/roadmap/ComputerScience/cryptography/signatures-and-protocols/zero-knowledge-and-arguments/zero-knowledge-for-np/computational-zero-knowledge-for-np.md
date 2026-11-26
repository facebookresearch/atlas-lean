# Every NP language has a computational zero-knowledge proof

Assume pseudorandom generators exist. For every NP language, the sequential repetition of the three-copy masked 3SAT protocol $k(n) = \omega(|\varphi| \log n)$ times is a computational zero-knowledge interactive proof: it is perfectly complete, has negligible soundness error against unbounded provers, and for every probabilistic polynomial-time (oracle) malicious verifier $V^*$ there is a probabilistic polynomial-time simulator whose output is computationally indistinguishable from the view of $V^*$ interacting with the honest prover, for every instance, witness and auxiliary input. The distinguishing advantage between the real and simulated views is bounded by a sum over the sessions of PRG advantages of an explicit single-challenge reduction plus the probability that the simulator's rewinding budget is exhausted.

## Proof sketch

The simulator guesses the verifier's challenge, commits to masked values that pass that check, and rewinds when the guess is wrong; unopened commitments hide their values by PRG security, so the verifier's challenge is almost independent of the guess. Across sessions, all unopened commitment pads are replaced by uniform strings in one hybrid reduction to the PRG.

## Depends on

- [The three-copy masked 3SAT zero-knowledge protocol](masked-3sat-zero-knowledge-protocol.md)
- [Zero-knowledge interactive proofs](../zero-knowledge-interactive-proofs.md)

## Proof depends on

- [Completeness and soundness of the masked 3SAT protocol](masked-3sat-completeness-soundness.md)

## Sources

- Oded Goldreich, Silvio Micali and Avi Wigderson, "Proofs that Yield Nothing but Their Validity or All Languages in NP Have Zero-Knowledge Proof Systems", Journal of the ACM, 1991.
- Oded Goldreich, "Foundations of Cryptography, Volume 2: Basic Applications", Cambridge University Press, 2004.
