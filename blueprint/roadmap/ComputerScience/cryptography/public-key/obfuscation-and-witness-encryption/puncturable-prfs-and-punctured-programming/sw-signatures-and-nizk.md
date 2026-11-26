# Short signatures and NIZK proofs from iO and one-way functions

Assume an indistinguishability obfuscator and one-way functions. Then (i) there is a selectively secure signature scheme with signatures of length $O(\lambda)$, where $\sigma=F(K,m)$ and the verification key is the obfuscation of the program checking $f(\sigma)=f(F(K,m))$ for a one-way function $f$; and (ii) every NP language has a perfectly zero-knowledge, selectively (computationally) sound non-interactive zero-knowledge argument in the common reference string model, where the reference string contains an obfuscated program that, on a valid statement-witness pair, outputs a PRF evaluation on the statement serving as the proof.

## Proof sketch

For signatures, puncture the PRF at the challenge message (selectively chosen) and hardwire $y^{*}=f(F(K,m^{*}))$; replacing $F(K,m^{*})$ by random, a forgery inverts $f$ on a random image. For NIZK, soundness for a selectively chosen false statement $x^{*}$ follows by puncturing the PRF at $x^{*}$ (the proving program never evaluates it there) and reducing a convincing proof to inverting $f$ on $f(F(K,x^{*}))$ with $F(K,x^{*})$ replaced by a random value, and zero knowledge follows by simulating proofs with the PRF key, using iO to switch between equivalent programs.

## Depends on

- [Zero-knowledge interactive proofs](../../../signatures-and-protocols/zero-knowledge-and-arguments/zero-knowledge-interactive-proofs.md)
- [Indistinguishability and virtual black-box obfuscation](../../../program-obfuscation/indistinguishability-and-virtual-black-box.md)

## Proof depends on

- [Punctured programming: swapping a program for a functionally equivalent punctured one](punctured-programming-hybrid.md)
- [The GGM construction is puncturable](ggm-is-puncturable.md)

## Sources

- Amit Sahai, Brent Waters, "How to Use Indistinguishability Obfuscation: Deniable Encryption, and More", STOC (2014), IACR ePrint 2013/454.
