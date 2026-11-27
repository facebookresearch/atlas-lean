# Quantum copy-protection and the impossibility of general quantum obfuscation

A *quantum copy-protection* scheme for a class $\mathcal{F}$ of classical functions maps $f\in\mathcal{F}$ to a quantum program $\rho_f$ from which $f(x)$ can be computed for every $x$, such that no efficient adversary, given one copy of $\rho_f$, can produce two (possibly entangled) programs that both compute $f$ correctly on independently sampled challenge inputs, beyond the trivial success probability. Copy-protection cannot exist for all unlearnable classes: assuming LWE (quantum-secure), there are unlearnable function families that cannot be copy-protected, and quantum virtual black-box obfuscation of classical circuits is impossible; positive results exist for specific classes (point functions, pseudorandom functions, decryption keys) using coset states, iO and random oracles.

## Depends on

- [Monogamy-of-entanglement property of coset states](coset-monogamy.md)
- [Impossibility of virtual black-box obfuscation](../program-obfuscation/impossibility-of-virtual-black-box-obfuscation.md)

## Sources

- Scott Aaronson, "Quantum Copy-Protection and Quantum Money", CCC (2009), arXiv:1110.5353.
- Scott Aaronson, Jiahui Liu, Qipeng Liu, Mark Zhandry, Ruizhe Zhang, "New Approaches for Quantum Copy-Protection", CRYPTO (2021).
- Gorjan Alagic, Zvika Brakerski, Yfke Dulek, Christian Schaffner, "Impossibility of Quantum Virtual Black-Box Obfuscation of Classical Circuits", CRYPTO (2021).
- Andrea Coladangelo, Jiahui Liu, Qipeng Liu, Mark Zhandry, "Hidden Cosets and Applications to Unclonable Cryptography", CRYPTO (2021), IACR ePrint 2021/946.
