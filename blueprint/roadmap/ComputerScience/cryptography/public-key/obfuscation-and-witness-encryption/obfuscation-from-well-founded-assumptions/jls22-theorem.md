# Indistinguishability obfuscation without lattices: LPN over F_p, DLIN and local PRGs

Assuming sub-exponential security of LPN over $\mathbb{Z}_p$ (with polynomially many samples and error rate $\ell^{-\delta}$), the decisional linear (DLIN) assumption in symmetric bilinear groups (or SXDH in asymmetric ones), and the existence of a PRG in $\mathsf{NC}^{0}$ with polynomial stretch, indistinguishability obfuscation for all polynomial-size circuits exists. In particular the LWE assumption can be removed from the well-founded-assumptions route to iO.

## Proof sketch

Replace the LWE-based noise flooding and outer encryption by a construction where the degree-2 computation's leakage is avoided altogether: build pseudorandom correlations and the needed bootstrapping directly from LPN over $\mathbb{Z}_p$ and the bilinear-map-based partially hiding FE, then apply compact-FE-to-iO bootstrapping.

## Depends on

- [Learning parity with noise over large prime fields with sparse errors](lpn-over-large-fields.md)
- [Pseudorandom generators in NC0 with polynomial stretch](local-prg.md)
- [The symmetric external Diffie–Hellman assumption](sxdh-assumption.md)
- [Indistinguishability and virtual black-box obfuscation](../../../program-obfuscation/indistinguishability-and-virtual-black-box.md)

## Proof depends on

- [Indistinguishability obfuscation from LWE, LPN over F_p, local PRGs and SXDH](jls-main-theorem.md)
- [Structured-seed PRGs from LPN over F_p and local PRGs](sprg-from-lpn-and-local-prg.md)
- [Indistinguishability obfuscation from sub-exponentially secure compact functional encryption](../compact-functional-encryption-to-obfuscation/fe-to-io-bootstrapping.md)

## Sources

- Aayush Jain, Huijia Lin, Amit Sahai, "Indistinguishability Obfuscation from LPN over F_p, DLIN, and PRGs in NC^0", EUROCRYPT (2022), IACR ePrint 2021/1334.
