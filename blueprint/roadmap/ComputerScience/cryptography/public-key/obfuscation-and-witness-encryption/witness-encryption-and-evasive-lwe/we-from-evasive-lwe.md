# Witness encryption and null-iO from evasive LWE

Assuming LWE and the evasive LWE assumption for an appropriate class of (private-coin) samplers, the GGH15-style candidate of Chen–Vaikuntanathan–Wee is a secure null-iO obfuscator for a class of branching programs sufficient to express NP verification, and hence yields witness encryption for all of NP. The construction encodes a matrix branching program through a chain of Gaussian preimages $\mathbf{B}_{i-1}^{-1}(\mathbf{S}_{i,b}\mathbf{B}_i+\mathbf{E}_{i,b})$, and evaluation on a witness computes a product that is small iff the branching program accepts.

## Proof sketch

Prove security by induction along the chain: at each step, the precondition of evasive LWE holds because the partially evaluated encodings are LWE samples with the remaining secret products, and the postcondition replaces the next preimage layer by one over random matrices. For null programs, every evaluation is a product of LWE-like terms, so all evaluations are pseudorandom, and the final distribution is independent of the program.

## Depends on

- [The evasive LWE assumption](evasive-lwe.md)
- [Null indistinguishability obfuscation](null-io.md)
- [Witness encryption for NP languages](witness-encryption.md)

## Proof depends on

- [Witness encryption from null indistinguishability obfuscation](we-from-null-io.md)

## Sources

- Vinod Vaikuntanathan, Hoeteck Wee, Daniel Wichs, "Witness Encryption and Null-IO from Evasive LWE", ASIACRYPT (2022).
- Yilei Chen, Vinod Vaikuntanathan, Hoeteck Wee, "GGH15 Beyond Permutation Branching Programs: Proofs, Attacks, and Candidates", CRYPTO (2018).
- Rotem Tsabary, "Candidate Witness Encryption from Lattice Techniques", CRYPTO (2022).
