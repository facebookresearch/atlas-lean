# Key-only unforgeability of ML-DSA from Module-LWE and SelfTargetMSIS

For every key-only forger $\mathcal{F}$ against ML-DSA (uncompressed or compressed public key, fixed or random-oracle hash), there are adversaries $\mathcal{D}$ and $\mathcal{S}$ whose running times exceed that of $\mathcal{F}$ by at most the time of computing the public key from their instance, answering the random-oracle queries of $\mathcal{F}$ by lazy sampling, and one ML-DSA verification, such that

$$
\Pr[\mathcal{F} \text{ forges}] \le \mathrm{Adv}^{\mathrm{mlwe}}_{k, \ell, \eta}(\mathcal{D}) + \Pr[\mathcal{S} \text{ solves SelfTargetMSIS for } [\,I \mid \mathbf{A} \mid \mathbf{t}\,]],
$$

where the Module-LWE instance has short secret and error laws uniform on $[-\eta, \eta]$ and the SelfTargetMSIS instance uses a uniform $\mathbf{t}$. Combined with the forking reduction from SelfTargetMSIS to Module-SIS, key-only security follows from decision Module-LWE and Module-SIS in the classical random oracle model.

## Proof sketch

Replace $\mathbf{t} = \mathbf{A}\mathbf{s}_1 + \mathbf{s}_2$ by a uniform vector at the cost of a Module-LWE advantage; the matrix may be drawn on demand from the random oracle at the public seed, which gives the same joint law. Then a forgery is a SelfTargetMSIS solution by the algebraic lemma.

## Depends on

- [The ML-DSA signature scheme](../ml-dsa-signatures/ml-dsa-scheme.md)
- [Decision Module-LWE](../../../public-key/lattice-and-code-based-cryptography/lattice-problems/decision-module-lwe.md)
- [The SelfTargetMSIS problem](../../../hash-functions/lattice-based-hashing/self-target-module-sis.md)
- [Signature schemes and (strong) unforgeability in the random oracle model](../../sigma-protocols-and-fiat-shamir/random-oracle-signatures/rom-signature-unforgeability.md)

## Proof depends on

- [A verifying ML-DSA forgery is a SelfTargetMSIS solution](ml-dsa-forgery-is-self-target-solution.md)
- [SelfTargetMSIS reduces to Module-SIS in the classical random oracle model](../../../hash-functions/lattice-based-hashing/self-target-msis-to-msis-by-forking.md)
- [Lazy and eager sampling of a random oracle are equivalent](../../../public-key/chosen-ciphertext-security/fujisaki-okamoto-kem-transforms/lazy-eager-random-oracle.md)

## Sources

- Shi Bai et al., "CRYSTALS-Dilithium: Algorithm Specifications and Supporting Documentation, Version 3.1", CRYSTALS Project, 2021.
- Léo Ducas et al., "CRYSTALS-Dilithium: A Lattice-Based Digital Signature Scheme", IACR Transactions on Cryptographic Hardware and Embedded Systems, 2018.
