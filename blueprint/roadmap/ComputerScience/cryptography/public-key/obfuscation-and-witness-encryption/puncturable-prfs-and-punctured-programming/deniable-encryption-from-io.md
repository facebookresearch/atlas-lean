# Publicly deniable encryption from indistinguishability obfuscation

A *publicly deniable* public-key encryption scheme has algorithms $\mathsf{Setup}$, $\mathsf{Encrypt}(PK,m;u)$ with explicit random coins $u$, $\mathsf{Decrypt}$ (correct except with negligible probability) and $\mathsf{Explain}(PK,c,m';r)$, which takes only the public key, a ciphertext and a message and outputs a string of the length of $u$. It is required to be IND-CPA secure and to have *indistinguishability of explanation*: for every message $m$ chosen by an efficient adversary after seeing $PK$, the pairs $(c,u)$ and $(c,\mathsf{Explain}(PK,c,m;r))$ with $c=\mathsf{Encrypt}(PK,m;u)$ are computationally indistinguishable. Assuming an indistinguishability obfuscator for all polynomial-size circuits and one-way functions, there is a publicly deniable public-key encryption scheme. The two properties together imply sender deniability in the sense of Canetti, Dwork, Naor and Ostrovsky with negligible distinguishing advantage, by setting the faking algorithm to $\mathsf{Explain}(PK,c,m')$; anyone, not only the sender, can produce fake randomness explaining a ciphertext as any message of their choice. This gives the first deniable encryption scheme that needs no pre-planning by the party that later issues a denial.

## Proof sketch

The public key includes an obfuscated program that, on inputs encoding a hidden trigger (an encrypted instruction derived from a PRF), outputs a specified ciphertext instead of encrypting freshly. Faking computes such a trigger for $(c,m')$; punctured programming at the trigger point and the challenge randomness shows real and fake openings are indistinguishable.

## Depends on

- [Indistinguishability and virtual black-box obfuscation](../../../program-obfuscation/indistinguishability-and-virtual-black-box.md)

## Proof depends on

- [Punctured programming: swapping a program for a functionally equivalent punctured one](punctured-programming-hybrid.md)
- [Public-key encryption from indistinguishability obfuscation and one-way functions](sw-pke-from-io.md)

## Sources

- Amit Sahai, Brent Waters, "How to Use Indistinguishability Obfuscation: Deniable Encryption, and More", STOC (2014), IACR ePrint 2013/454, abstract and Section 2 (Definitions 1-4).
