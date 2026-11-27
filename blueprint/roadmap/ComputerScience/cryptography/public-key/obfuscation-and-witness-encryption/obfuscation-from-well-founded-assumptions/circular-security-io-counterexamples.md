# Counterexamples to the circular-security assumptions behind lattice-based iO candidates

The lattice-based iO constructions of Gay–Pass and of Wee–Wichs rely on new circular-security-style assumptions about LWE-based encryption: Gay–Pass on a $2$-circular shielded-randomness-leakage assumption for GSW encryption, and Wee–Wichs on a conjecture that homomorphically evaluated LWE samples are pseudorandom. There exist explicit (contrived but syntactically valid) instantiations of the encryption schemes and leakage functions allowed by those assumptions for which the assumptions, as stated, are false: an efficient adversary distinguishes the real distribution from the ideal one. Hence the general forms of these assumptions do not hold, and security of the resulting candidates requires restricting the class of schemes or relying on heuristic instantiations. The variant of the Gay–Pass assumption with a key-randomness cycle used by Brakerski–Döttling–Garg–Malavolta is not refuted by these counterexamples, and the iO schemes themselves remain unbroken.

## Proof sketch

Construct a scheme in which encryptions of the secret key combined with the permitted homomorphic evaluations allow computing, via low-norm linear combinations, a quantity whose distribution differs between the circular-secure and the ideal worlds (for instance, by embedding a trapdoor-revealing structure that only appears when the key is encrypted under itself). Verify that the scheme satisfies all conditions imposed by the assumptions.

## Depends on

- [Indistinguishability and virtual black-box obfuscation](../../../program-obfuscation/indistinguishability-and-virtual-black-box.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)
- [Circular security from fully composable homomorphic encryption](../../circular-security-from-composable-homomorphic-encryption.md)

## Sources

- Sam Hopkins, Aayush Jain, Huijia Lin, "Counterexamples to New Circular Security Assumptions Underlying iO", CRYPTO (2021), IACR ePrint 2021/889, Section 1.
- Romain Gay, Rafael Pass, "Indistinguishability Obfuscation from Circular Security", STOC (2021), IACR ePrint 2020/1010.
- Hoeteck Wee, Daniel Wichs, "Candidate Obfuscation via Oblivious LWE Sampling", EUROCRYPT (2021), IACR ePrint 2020/1042.
- Zvika Brakerski, Nico Döttling, Sanjam Garg, Giulio Malavolta, "Factoring and Pairings Are Not Necessary for IO: Circular-Secure LWE Suffices", ICALP (2022), IACR ePrint 2020/1024.
