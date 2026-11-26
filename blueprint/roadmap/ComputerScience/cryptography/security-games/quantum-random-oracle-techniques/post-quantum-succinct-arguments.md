# Post-quantum security of Kilian's succinct arguments

Assuming collapsing hash functions (e.g., from LWE), Kilian's four-message succinct argument for NP, obtained by committing to a PCP with a Merkle tree and opening the verifier's queries, is a post-quantum succinct argument of knowledge: every quantum polynomial-time prover that convinces the verifier with non-negligible probability can be used to extract a witness. In the QROM, Micali's non-interactive CS proofs are likewise sound against quantum adversaries.

## Proof sketch

The obstacle is rewinding a quantum prover across many challenges, since measuring openings disturbs its state. The proof develops a state-repair procedure (based on Marriott–Watrous amplification and collapsing) that restores the prover's success probability after each measured opening, allowing polynomially many rewinds to recover enough PCP positions to decode a witness. In the QROM, compressed-oracle techniques bound the probability of inconsistent Merkle openings.

## Depends on

- [Collapsing hash functions and collapse-binding commitments](collapsing-hash.md)
- [The quantum random oracle model](quantum-random-oracle-model.md)
- [Succinct arguments and SNARKs](../../signatures-and-protocols/zero-knowledge-and-arguments/succinct-arguments-and-snarks.md)
- [Knowledge soundness](../../signatures-and-protocols/zero-knowledge-and-arguments/knowledge-soundness.md)

## Proof depends on

- [Random oracles and LWE-based hashes are collapsing](collapsing-from-random-oracle-and-lwe.md)
- [Unruh's quantum rewinding lemma for special-sound protocols](unruh-rewinding.md)
- [Succinct arguments from probabilistically checkable proofs](../../signatures-and-protocols/zero-knowledge-and-arguments/succinct-arguments-from-probabilistically.md)

## Sources

- Alessandro Chiesa, Fermi Ma, Nicholas Spooner, Mark Zhandry, "Post-Quantum Succinct Arguments: Breaking the Quantum Rewinding Barrier", FOCS (2021).
- Alessandro Chiesa, Peter Manohar, Nicholas Spooner, "Succinct Arguments in the Quantum Random Oracle Model", TCC (2019).
