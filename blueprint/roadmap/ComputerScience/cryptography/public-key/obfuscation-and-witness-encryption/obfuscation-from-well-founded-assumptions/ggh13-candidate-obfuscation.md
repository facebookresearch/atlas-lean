# Candidate obfuscation for all circuits from multilinear maps

There is a candidate construction of indistinguishability obfuscation for all polynomial-size circuits, obtained by obfuscating matrix branching programs for $\mathsf{NC}^{1}$ with randomized encodings in a graded (multilinear) encoding scheme, and bootstrapping from $\mathsf{NC}^{1}$ to $\mathsf{P}/\mathsf{poly}$ using fully homomorphic encryption and a low-depth decryption-and-proof-checking circuit. Combined with iO, this yields functional encryption for all circuits. The security of the original candidate rests on idealized assumptions about the multilinear encoding, which later analysis showed to be subject to various attacks for specific instantiations.

## Proof sketch

Kilian-randomize the branching program matrices, encode them at levels so that only honest evaluations reach the top level where zero-testing reveals the output; bootstrapping uses an FHE-encrypted circuit and an obfuscated $\mathsf{NC}^{1}$ program that decrypts only given a proof of honest evaluation.

## Depends on

- [Indistinguishability and virtual black-box obfuscation](../../../program-obfuscation/indistinguishability-and-virtual-black-box.md)
- [Homomorphic encryption: correctness and compactness](../../homomorphic-encryption/homomorphic-encryption-correctness-and.md)

## Proof depends on

- [Impossibility of virtual black-box obfuscation](../../../program-obfuscation/impossibility-of-virtual-black-box-obfuscation.md)

## Sources

- Sanjam Garg, Craig Gentry, Shai Halevi, Mariana Raykova, Amit Sahai, Brent Waters, "Candidate Indistinguishability Obfuscation and Functional Encryption for All Circuits", FOCS (2013).
