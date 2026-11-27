# Counterexamples to general forms of private-coin evasive LWE

The private-coin evasive LWE assumption does not hold for all efficient samplers. Assuming LWE, there exist explicit private-coin samplers for which the precondition holds but the postcondition fails: given $\mathbf{B}^{-1}(\mathbf{P})$ and $\mathsf{aux}$, an efficient adversary distinguishes $\mathbf{s}^{\top}\mathbf{B}+\mathbf{e}^{\top}$ from uniform (Brzuska–Ünal–Woo). These refute three private-coin variants used in earlier constructions, among them the general form of the Vaikuntanathan–Wee–Wichs assumption; in one of the counterexamples $\mathbf{P}$ is not given to the distinguisher, $\mathsf{aux}$ is empty, and a trapdoor is planted in part of $\mathbf{P}$. Assuming LWE and null-iO, a sampler whose $\mathsf{aux}$ is an obfuscated program refutes private-coin evasive LWE in general (Brzuska–Ünal–Woo), making rigorous the heuristic counterexample of Vaikuntanathan–Wee–Wichs, which assumes an ideal obfuscation. Neither applies to public-coin samplers. Consequently evasive LWE must be stated relative to restricted sampler classes (such as public-coin samplers or specific structured families), and the security of constructions relying on it must be argued with respect to those restricted forms.

## Proof sketch

Hide structure in the private coins: plant a trapdoor in the part of $\mathbf{P}$ that the distinguisher never sees, or give in $\mathsf{aux}$ an obfuscated program that knows $\mathbf{P}$. The precondition still holds, by LWE (and by the security of the obfuscation), because the planted structure is not visible from $\mathbf{s}^{\top}\mathbf{P}+\mathbf{e}_2^{\top}$ and $\mathsf{aux}$ alone. Combined with the preimage $\mathbf{K}=\mathbf{B}^{-1}(\mathbf{P})$, however, it lets the distinguisher compute from $\mathbf{s}^{\top}\mathbf{B}+\mathbf{e}^{\top}$ a quantity that is small only in the real case.

## Depends on

- [The evasive LWE assumption](evasive-lwe.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)
- [Null indistinguishability obfuscation](null-io.md)

## Sources

- Vinod Vaikuntanathan, Hoeteck Wee, Daniel Wichs, "Witness Encryption and Null-IO from Evasive LWE", ASIACRYPT (2022), IACR ePrint 2022/1140, Section 8.2.
- Chris Brzuska, Akin Ünal, Ivy K. Y. Woo, "Evasive LWE Assumptions: Definitions, Classes, and Counterexamples", ASIACRYPT (2024), IACR ePrint 2024/2000, Sections 5 and 7.
