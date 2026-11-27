# Indistinguishability obfuscation from LWE, LPN over F_p, local PRGs and SXDH

Let $\tau\in(0,\infty)$, $\delta,\epsilon\in(0,1)$ be constants, $\lambda$ the security parameter and $p$ a $\lambda$-bit prime. Assume sub-exponential security of: (1) LWE over $\mathbb{Z}_p$ with sub-exponential modulus-to-noise ratio $2^{k^{\epsilon}}$, where $k$ is the dimension of the secret; (2) LPN over $\mathbb{Z}_p$ with polynomially many samples and error rate $\ell^{-\delta}$, where $\ell$ is the dimension; (3) the existence of a PRG in $\mathsf{NC}^{0}$ with stretch $n^{1+\tau}$; and (4) SXDH in asymmetric bilinear groups. Then indistinguishability obfuscation for all polynomial-size circuits exists. Consequently, under these assumptions, all primitives known to follow from iO and one-way functions exist, including functional encryption for all circuits and non-interactive witness-indistinguishable proofs.

## Proof sketch

Combine the structured-seed PRG from LPN and the local PRG, the partially hiding FE from SXDH, and LWE-based encryption with noise flooding to obtain single-key weakly compact public-key FE with sub-exponential security. Bootstrap to iO via the compact-FE-to-iO theorem, using complexity leveraging for the exponentially many hybrids.

## Depends on

- [The symmetric external Diffie–Hellman assumption](sxdh-assumption.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)
- [Indistinguishability and virtual black-box obfuscation](../../../program-obfuscation/indistinguishability-and-virtual-black-box.md)
- [Pseudorandom generators in NC0 with polynomial stretch](local-prg.md)
- [Learning parity with noise over large prime fields with sparse errors](lpn-over-large-fields.md)

## Proof depends on

- [Structured-seed PRGs from LPN over F_p and local PRGs](sprg-from-lpn-and-local-prg.md)
- [Sublinear functional encryption from partially hiding FE and structured-seed PRGs](../compact-functional-encryption-to-obfuscation/sublinear-fe-from-phfe.md)
- [Indistinguishability obfuscation from sub-exponentially secure compact functional encryption](../compact-functional-encryption-to-obfuscation/fe-to-io-bootstrapping.md)

## Sources

- Aayush Jain, Huijia Lin, Amit Sahai, "Indistinguishability Obfuscation from Well-Founded Assumptions", STOC (2021), IACR ePrint 2020/1003, arXiv:2008.09317.
