# Counterexamples to general forms of private-coin evasive LWE

The private-coin evasive LWE assumption does not hold for all efficient samplers. Assuming LWE, there exist explicit private-coin samplers for which the precondition holds but the postcondition fails: given $\mathbf{B}^{-1}(\mathbf{P})$ and $\mathsf{aux}$, an efficient adversary distinguishes $\mathbf{s}^{\top}\mathbf{B}+\mathbf{e}^{\top}$ from uniform (Brzuska–Ünal–Woo, ASIACRYPT 2024, Section 5). These refute three private-coin variants used in earlier constructions, among them the general form of the Vaikuntanathan–Wee–Wichs assumption; in one of the counterexamples $\mathbf{P}$ is not given to the distinguisher, $\mathsf{aux}$ is empty, and a trapdoor is planted in part of $\mathbf{P}$. (Vaikuntanathan–Wee–Wichs, Section 8.2, also proposed a heuristic attack using an ideal obfuscation in $\mathsf{aux}$, though Huang–Hung–Yamada showed that this obfuscation-based attack does not work and that private-coin evasive LWE remains open when the sampler does not know the LWE secret.) None of these LWE-based counterexamples applies to public-coin samplers. Consequently evasive LWE must be stated relative to restricted sampler classes (such as public-coin samplers or specific structured families), and the security of constructions relying on it must be argued with respect to those restricted forms.

## Proof sketch

Hide structure in the private coins by planting a trapdoor in the part of $\mathbf{P}$ that the distinguisher never sees (Brzuska–Ünal–Woo, Section 5). The precondition still holds under LWE because the planted structure is hidden in $\mathbf{s}^{\top}\mathbf{P}+\mathbf{e}_2^{\top}$ and $\mathsf{aux}$ alone. Combined with the preimage $\mathbf{K}=\mathbf{B}^{-1}(\mathbf{P})$, however, the planted trapdoor lets the distinguisher compute from $\mathbf{s}^{\top}\mathbf{B}+\mathbf{e}^{\top}$ a quantity that is small only in the real case.

## Depends on

- [The evasive LWE assumption](evasive-lwe.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Sources

- Vinod Vaikuntanathan, Hoeteck Wee, Daniel Wichs, "Witness Encryption and Null-IO from Evasive LWE", ASIACRYPT (2022), IACR ePrint 2022/1140, Section 8.2.
- Chris Brzuska, Akin Ünal, Ivy K. Y. Woo, "Evasive LWE Assumptions: Definitions, Classes, and Counterexamples", ASIACRYPT (2024), IACR ePrint 2024/2000, Section 5.
- Shih-Han Huang, Yao-Ching Hung, Shota Yamada, "A Note on Obfuscation-Based Attacks on Private-Coin Evasive LWE", IACR Communications in Cryptology 2(4).
