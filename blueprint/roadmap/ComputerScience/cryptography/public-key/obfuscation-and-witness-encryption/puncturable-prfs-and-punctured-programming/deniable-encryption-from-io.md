# Publicly deniable encryption from indistinguishability obfuscation

Assuming indistinguishability obfuscation and one-way functions, there is a publicly deniable public-key encryption scheme: for any ciphertext $c$ encrypting $m$ with randomness $r$ and any message $m'$, an efficient algorithm (using only public information, $m$, $r$ and $m'$) produces randomness $r'$ such that $(c,r')$ is computationally indistinguishable from an honest encryption of $m'$ together with its true randomness. This resolves the problem of constructing deniable encryption with negligible detection advantage.

## Proof sketch

The public key includes an obfuscated program that, on inputs encoding a hidden trigger (an encrypted instruction derived from a PRF), outputs a specified ciphertext instead of encrypting freshly. Faking computes such a trigger for $(c,m')$; punctured programming at the trigger point and the challenge randomness shows real and fake openings are indistinguishable.

## Depends on

- [Indistinguishability and virtual black-box obfuscation](../../../program-obfuscation/indistinguishability-and-virtual-black-box.md)

## Proof depends on

- [Punctured programming: swapping a program for a functionally equivalent punctured one](punctured-programming-hybrid.md)
- [Public-key encryption from indistinguishability obfuscation and one-way functions](sw-pke-from-io.md)

## Sources

- Amit Sahai, Brent Waters, "How to Use Indistinguishability Obfuscation: Deniable Encryption, and More", STOC (2014), IACR ePrint 2013/454.
