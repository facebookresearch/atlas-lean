# Sigma protocols are round-by-round sound public-coin interactive proofs

Every Sigma protocol with a nonempty finite challenge set $C$ is a three-message public-coin interactive proof. If it is complete, the interactive proof is perfectly complete; if it is 2-special sound, the interactive verifier is round-by-round sound with challenge error $1/|C|$ and sound against arbitrary unbounded provers with error $1/|C|$. Hence, by the Fiat–Shamir and BCS-type compilers for round-by-round sound protocols, its non-interactive version is sound in the random oracle model with error linear in the number of oracle queries times $1/|C|$.

## Proof sketch

Declare a partial transcript doomed if the statement is false and, for the commitment sent, no challenge or at most one challenge admits an accepting response; special soundness shows a doomed state stays doomed except with probability $1/|C|$ over the challenge.

## Depends on

- [A Sigma protocol](../../zero-knowledge-proofs/sigma-protocol.md)
- [Special soundness of a Sigma protocol](../../zero-knowledge-proofs/special-sound.md)
- [Zero-knowledge interactive proofs](../../zero-knowledge-and-arguments/zero-knowledge-interactive-proofs.md)

## Proof depends on

- [Language reductions transfer soundness of Sigma protocols](sigma-language-reductions.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
- Alessandro Chiesa and Eylon Yogev, "Building Cryptographic Proofs from Hash Functions", 2024.
