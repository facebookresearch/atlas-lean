# Public-key encryption from indistinguishability obfuscation and one-way functions

Assume an indistinguishability obfuscator for polynomial-size circuits and one-way functions. Let $\mathrm{PRG}:\{0,1\}^{\lambda}\to\{0,1\}^{2\lambda}$ and $F$ a puncturable PRF with output length $\ell$. The scheme with secret key $K$, public key $\mathcal{O}(\mathsf{Enc}_K)$ where $\mathsf{Enc}_K(m,r)=(t,F(K,t)\oplus m)$ with $t=\mathrm{PRG}(r)$, and decryption $m=c\oplus F(K,t)$, is IND-CPA secure. Hence iO together with one-way functions implies public-key encryption, moving from Minicrypt to Cryptomania.

## Proof sketch

In the challenge, replace $t^{*}=\mathrm{PRG}(r^{*})$ by a uniform $2\lambda$-bit string (PRG security); with overwhelming probability $t^{*}$ is outside the PRG's image, so the obfuscated program never queries $F(K,t^{*})$ and can be replaced by the program with punctured key (punctured programming). Then $F(K,t^{*})$ is pseudorandom, so the ciphertext component hides $m$.

## Depends on

- [Minicrypt](../../../../../TheoryOfComputation/pseudorandomness-and-one-way-functions/impagliazzo-s-five-worlds/minicrypt.md)
- [Puncturable pseudorandom functions](puncturable-prf.md)
- [Indistinguishability and virtual black-box obfuscation](../../../program-obfuscation/indistinguishability-and-virtual-black-box.md)
- [One-way function families](../../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Proof depends on

- [Punctured programming: swapping a program for a functionally equivalent punctured one](punctured-programming-hybrid.md)
- [The GGM construction is puncturable](ggm-is-puncturable.md)
- [Pseudorandom generators exist if and only if one-way functions exist](../../../symmetric-key/pseudorandom-generators/pseudorandom-generators-exist-if-and-only-if.md)

## Sources

- Amit Sahai, Brent Waters, "How to Use Indistinguishability Obfuscation: Deniable Encryption, and More", STOC (2014), IACR ePrint 2013/454.
