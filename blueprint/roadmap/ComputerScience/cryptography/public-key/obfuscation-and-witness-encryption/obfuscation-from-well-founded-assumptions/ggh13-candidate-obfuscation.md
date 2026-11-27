# Candidate obfuscation for all circuits from multilinear maps

(Bootstrapping.) If there are an indistinguishability obfuscator for $\mathsf{NC}^{1}$ circuits and a perfectly correct fully homomorphic encryption scheme whose decryption is computable in $\mathsf{NC}^{1}$, then there is an indistinguishability obfuscator for all polynomial-size circuits; the construction also uses perfectly sound non-interactive proofs whose verifier is in $\mathsf{NC}^{1}$, which exist unconditionally (the proof lists the values of all wires of the verification circuit). (Functional encryption.) An indistinguishability obfuscator for all polynomial-size circuits, together with a perfectly correct public-key encryption scheme and a statistically simulation-sound non-interactive zero-knowledge proof system for $\mathsf{NP}$, yields a functional encryption scheme for all polynomial-size circuits that is selectively secure in the indistinguishability game against adversaries obtaining polynomially many keys. Garg, Gentry, Halevi, Raykova, Sahai and Waters also give a candidate indistinguishability obfuscator for $\mathsf{NC}^{1}$, obfuscating randomized matrix branching programs encoded in multilinear jigsaw puzzles (a simplified variant of multilinear maps), whose security rests on a new algebraic hardness assumption rather than a proof; combined with the bootstrapping theorem it gives a candidate iO for all polynomial-size circuits. Later analysis showed that specific instantiations of the underlying multilinear encodings are subject to various attacks.

## Proof sketch

Bootstrapping: publish two FHE encryptions of the circuit under independent keys and an obfuscated $\mathsf{NC}^{1}$ program that, given two evaluated ciphertexts and a low-depth proof that both were computed honestly from the input, decrypts one of them; a hybrid argument switches the encrypted circuits and the decryption key one at a time, using the security of the FHE scheme, the perfect soundness of the proof, the perfect correctness of the FHE scheme and the security of the $\mathsf{NC}^{1}$ obfuscator. Functional encryption: a ciphertext consists of two public-key encryptions of the message and a simulation-sound proof that they encrypt the same message, and a key for $f$ is an obfuscated program that checks the proof, decrypts one encryption and outputs $f$ of the message. The candidate Kilian-randomizes branching program matrices and encodes them so that only honest evaluations reach the top level, where zero-testing reveals the output.

## Depends on

- [Indistinguishability and virtual black-box obfuscation](../../../program-obfuscation/indistinguishability-and-virtual-black-box.md)
- [Homomorphic encryption: correctness and compactness](../../homomorphic-encryption/homomorphic-encryption-correctness-and.md)

## Sources

- Sanjam Garg, Craig Gentry, Shai Halevi, Mariana Raykova, Amit Sahai, Brent Waters, "Candidate Indistinguishability Obfuscation and Functional Encryption for All Circuits", FOCS (2013), IACR ePrint 2013/451, abstract, Sections 5 and 6 (Theorems 3 and 4).
