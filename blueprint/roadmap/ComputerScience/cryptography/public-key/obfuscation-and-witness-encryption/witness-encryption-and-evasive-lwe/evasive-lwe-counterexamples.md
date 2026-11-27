# Counterexamples to general forms of private-coin evasive LWE

The private-coin evasive LWE assumption does not hold for all efficient samplers. There exist samplers (for instance, ones embedding an obfuscated program or structured auxiliary information correlated with $\mathbf{P}$) for which the precondition holds but the postcondition fails: given $\mathbf{B}^{-1}(\mathbf{P})$ and $\mathsf{aux}$, an efficient adversary distinguishes $\mathbf{s}^{\top}\mathbf{B}+\mathbf{e}^{\top}$ from uniform. Consequently evasive LWE must be stated relative to restricted sampler classes (such as public-coin samplers or specific structured families), and the security of constructions relying on it must be argued with respect to those restricted forms.

## Proof sketch

Design $\mathsf{aux}$ so that it is pseudorandom on its own (making the precondition hold under LWE or iO), yet combining it with the preimage $\mathbf{K}$ and the sample $\mathbf{s}^{\top}\mathbf{B}+\mathbf{e}^{\top}$ allows computing a quantity that is small only in the real case, e.g., by having $\mathsf{aux}$ encode a short vector in a lattice related to $\mathbf{P}$ that becomes useful only together with $\mathbf{K}$.

## Depends on

- [The evasive LWE assumption](evasive-lwe.md)

## Sources

- Vinod Vaikuntanathan, Hoeteck Wee, Daniel Wichs, "Witness Encryption and Null-IO from Evasive LWE", ASIACRYPT (2022).
- Chris Brzuska, Akin Ünal, Ivy K. Y. Woo, "Evasive LWE Assumptions: Definitions, Classes, and Counterexamples", ASIACRYPT (2024).
