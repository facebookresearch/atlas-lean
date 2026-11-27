# Succinct arguments from probabilistically checkable proofs

Let $L \in \mathsf{NP}$ have a probabilistically checkable proof whose verifier uses $O(\log n)$ random bits and makes polylogarithmically many queries, so that proofs have polynomial length; the PCP theorem gives such a verifier with a constant number of queries. If collision-resistant hash families exist, then $L$ has a four-message public-coin interactive argument in which the verifier first sends a key of the collision-resistant family, the prover commits to the PCP proof by the root of a Merkle tree built with that key, the verifier sends its PCP randomness, and the prover opens the queried positions with their authentication paths. The prover and verifier run in the time of the PCP prover and verifier up to low-order factors, the communication is $O(\log n)$ hash values per PCP query, hence polylogarithmic in the instance size times the security parameter, and soundness holds against efficient provers: after the commit phase each queried position has at most one value the prover can open without finding a hash collision, so an accepting prover yields a proof string accepted by the PCP verifier.

Polynomial interactive oracle proofs are compiled the same way, by replacing each polynomial sent as an oracle with a polynomial commitment scheme and each evaluation query with an evaluation proof; applying the Fiat–Shamir transformation to the resulting public-coin argument removes interaction. Soundness of that compiler is a separate statement.

## Depends on

- [Succinct arguments and SNARKs](succinct-arguments-and-snarks.md)
- [Polynomial commitment schemes](polynomial-commitment-schemes.md)
- [Polynomial-time many-one reduction](../../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md)

## Proof depends on

- [Completeness of Merkle inclusion proofs](../../hash-functions/merkle-trees/verify-auth-path.md)
- [Constructive soundness of Merkle inclusion proofs](../../hash-functions/merkle-trees/verify-sound-find-collision.md)

## Sources

- J. Thaler, *Proofs, Arguments, and Zero-Knowledge*, Foundations and Trends in Privacy and Security 4(2–4), 2022, <https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf>: Section 9.2 (Kilian's four-message argument from a PCP and Merkle hashing, with its completeness and soundness arguments and Remark 9.4) and Section 10.2 (the polynomial IOP plus polynomial commitment plus Fiat–Shamir recipe).
- J. Kilian, "A note on efficient zero-knowledge proofs and arguments", *Proceedings of the 24th ACM STOC*, 1992.
