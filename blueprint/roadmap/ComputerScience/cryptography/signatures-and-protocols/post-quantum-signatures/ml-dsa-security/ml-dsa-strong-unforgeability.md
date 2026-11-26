# Strong unforgeability of ML-DSA in the random oracle model

Model the hash and expansion functions of ML-DSA (FIPS 204, including the SHAKE-based matrix, mask, secret and challenge expansion with the Appendix C caps on attempts and output lengths) as random oracles. For every strong chosen-message forger $\mathcal{F}$ making $q_S$ signing queries and $q_H$ hash queries, the success probability of $\mathcal{F}$ is at most the sum of: the key-only bound (a Module-LWE advantage plus a SelfTargetMSIS success probability); the Module-SIS advantage for distinct responses at a repeated challenge; the statistical loss of replacing every signing attempt by the public simulation with a programmed commitment digest, which in the classical random oracle model is bounded in terms of the commitment guessing probability and the abort probability as in Barbosa et al., Theorem 3 (Theorem 4 for Dilithium); the probability of predicting the private signing seed or the private mask seeds; and the probability that some signing request exhausts the cap on signing attempts (FIPS 204, Appendix C, sets the cap so that one request reaches it with probability about $2^{-256}$ or less). The Module-LWE, SelfTargetMSIS and Module-SIS terms are those of the SUF-CMA bound of the Dilithium specification, Section 6.2, Equation (6); the seed and cap terms account for the seeded expansion and the caps of FIPS 204. For a quantum adversary making quantum hash queries, the reprogramming loss is bounded as in Fallahpour, Fehr and Huang, Theorem 1.

## Proof sketch

A sequence of game hops: make the private seeds of the signer independent of the oracle (seed-prediction loss), replace each signing attempt by the public simulation and program the commitment hash at its input (reprogramming loss, bounded by commitment entropy, classically by a union bound and quantumly by the one-way-to-hiding style reprogramming bound), and finally apply the key-only reduction and the response-binding lemma to the forgery.

## Depends on

- [The ML-DSA signature scheme](../ml-dsa-signatures/ml-dsa-scheme.md)
- [Signature schemes and (strong) unforgeability in the random oracle model](../../sigma-protocols-and-fiat-shamir/random-oracle-signatures/rom-signature-unforgeability.md)
- [Decision Module-LWE](../../../public-key/lattice-and-code-based-cryptography/lattice-problems/decision-module-lwe.md)
- [Module-SIS and Ring-SIS](../../../public-key/lattice-and-code-based-cryptography/lattice-problems/module-sis.md)

## Proof depends on

- [Key-only unforgeability of ML-DSA from Module-LWE and SelfTargetMSIS](ml-dsa-key-only-security.md)
- [Distinct responses to the same ML-DSA challenge give a Module-SIS solution](ml-dsa-response-binding.md)
- [Simulation of ML-DSA signing attempts](../ml-dsa-signatures/ml-dsa-signing-simulation.md)
- [Lazy and eager sampling of a random oracle are equivalent](../../../public-key/chosen-ciphertext-security/fujisaki-okamoto-kem-transforms/lazy-eager-random-oracle.md)

## Sources

- Shi Bai et al., "CRYSTALS-Dilithium: Algorithm Specifications and Supporting Documentation, Version 3.1", CRYSTALS Project, 2021.
- Manuel Barbosa et al., "Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium", Cryptology ePrint Archive, Paper 2023/246, 2023.
- Pouria Fallahpour, Serge Fehr and Yu-Hsuan Huang, "Tighter Quantum Security for Fiat-Shamir-with-Aborts and Hash-and-Sign-with-Retry Signatures", Cryptology ePrint Archive, Paper 2025/985, 2025.
- National Institute of Standards and Technology, "Module-Lattice-Based Digital Signature Standard", National Institute of Standards and Technology, 2024.
