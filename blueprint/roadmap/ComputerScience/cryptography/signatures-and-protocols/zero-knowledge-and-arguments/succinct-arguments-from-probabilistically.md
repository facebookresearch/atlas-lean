# Succinct arguments from probabilistically checkable proofs

Let $L \in \mathsf{NP}$ have a probabilistically checkable proof with polylogarithmic query complexity. If collision-resistant hash families exist, then $L$ has a four-message public-coin interactive argument in which the verifier first sends a key of the collision-resistant family, the prover commits to the PCP proof by the root of a Merkle tree built with that key, the verifier sends its PCP randomness, and the prover opens the queried positions with their authentication paths; the total communication is polylogarithmic in the instance size (times the security parameter), and soundness holds against efficient provers. In the same way, a polynomial interactive oracle proof compiled with a polynomial commitment scheme gives a succinct argument whose soundness reduces to that of the interactive oracle proof and the evaluation binding of the commitment; knowledge soundness requires an extractable commitment.

## Depends on

- [Succinct arguments and SNARKs](succinct-arguments-and-snarks.md)
- [Polynomial commitment schemes](polynomial-commitment-schemes.md)
- [Polynomial-time many-one reduction](../../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md)

## Proof depends on

- [Completeness of Merkle inclusion proofs](../../hash-functions/merkle-trees/verify-auth-path.md)
- [Constructive soundness of Merkle inclusion proofs](../../hash-functions/merkle-trees/verify-sound-find-collision.md)

## Sources

- J. Kilian, "A note on efficient zero-knowledge proofs and arguments", *Proceedings of the 24th ACM STOC*, 1992
- J. Thaler, *Proofs, Arguments, and Zero-Knowledge*, Foundations and Trends in Privacy and Security 4(2–4), 2022, <https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf>
