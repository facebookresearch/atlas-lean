# Null indistinguishability obfuscation

A *null-iO* obfuscator for a circuit class $\mathcal{C}$ is a probabilistic polynomial-time algorithm $\mathcal{O}$ preserving functionality, $\mathcal{O}(C)(x)=C(x)$, such that for any two *null* circuits $C_0,C_1\in\mathcal{C}$ of the same size, i.e., circuits outputting $0$ on every input, $\mathcal{O}(C_0)\approx_c\mathcal{O}(C_1)$. Null-iO is the restriction of indistinguishability obfuscation to pairs of circuits that both compute the constant-zero function.

## Depends on

- [Indistinguishability and virtual black-box obfuscation](../../../program-obfuscation/indistinguishability-and-virtual-black-box.md)

## Sources

- Vinod Vaikuntanathan, Hoeteck Wee, Daniel Wichs, "Witness Encryption and Null-IO from Evasive LWE", ASIACRYPT (2022).
