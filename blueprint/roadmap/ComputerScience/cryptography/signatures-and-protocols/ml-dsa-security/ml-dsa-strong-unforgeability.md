# Strong unforgeability of ML-DSA in the random oracle model

Model the hash and expansion functions of ML-DSA (FIPS 204, including the SHAKE-based matrix, mask, secret and challenge expansion with the Appendix C caps on attempts and output lengths) as random oracles. For every strong chosen-message forger $\mathcal{F}$ making $q_S$ signing queries and $q_H$ hash queries, the success probability of $\mathcal{F}$ is at most the sum of: the key-only bound (a Module-LWE advantage plus a SelfTargetMSIS success probability); the Module-SIS advantage for distinct responses at a repeated challenge; the statistical loss of replacing every signing attempt by the public simulation with a programmed commitment digest, which is at most $q_S \kappa_{\max}$ times the largest commitment-atom probability times the number of prior oracle queries; the probability of predicting the private signing seed or the private mask seeds, of order $(q_H + 1)\,2^{-256}$ classically; and the probability that some signing request exhausts the attempt cap. For a quantum adversary making $T$ coherent queries, programming one fresh commitment costs at most of order $T$ times the square root of the largest commitment atom, and seed prediction after $j$ coherent queries succeeds with probability at most $(\sqrt{2 \cdot 2^{-256}} + 2j\, 2^{-128})^2$.

## Proof sketch

A sequence of game hops: make the private seeds of the signer independent of the oracle (seed-prediction loss), replace each signing attempt by the public simulation and program the commitment hash at its input (reprogramming loss, bounded by commitment entropy, classically by a union bound and quantumly by the one-way-to-hiding style reprogramming bound), and finally apply the key-only reduction and the response-binding lemma to the forgery.

## Depends on

- [The ML-DSA signature scheme](../ml-dsa-signatures/ml-dsa-scheme.md)
- [Signature schemes and (strong) unforgeability in the random oracle model](../random-oracle-signatures/rom-signature-unforgeability.md)
- [Decision Module-LWE](../../public-key/lattice-problems/decision-module-lwe.md)
- [Module-SIS and Ring-SIS](../../public-key/lattice-problems/module-sis.md)

## Proof depends on

- [Key-only unforgeability of ML-DSA from Module-LWE and SelfTargetMSIS](ml-dsa-key-only-security.md)
- [Distinct responses to the same ML-DSA challenge give a Module-SIS solution](ml-dsa-response-binding.md)
- [Simulation of ML-DSA signing attempts](../ml-dsa-signatures/ml-dsa-signing-simulation.md)
- [Lazy and eager sampling of a random oracle are equivalent](../../public-key/fujisaki-okamoto-kem-transforms/lazy-eager-random-oracle.md)

## Sources

- Shi Bai et al., "CRYSTALS-Dilithium: Algorithm Specifications and Supporting Documentation, Version 3.1", CRYSTALS Project, 2021.
- Manuel Barbosa et al., "Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium", Cryptology ePrint Archive, Paper 2023/246, 2023.
- Pouria Fallahpour, Serge Fehr and Yu-Hsuan Huang, "Tighter Quantum Security for Fiat-Shamir-with-Aborts and Hash-and-Sign-with-Retry Signatures", Cryptology ePrint Archive, Paper 2025/985, 2025.
- National Institute of Standards and Technology, "Module-Lattice-Based Digital Signature Standard", National Institute of Standards and Technology, 2024.
