# Indistinguishability obfuscation implies hardness of finding Nash equilibria

Assume a (sub-exponentially secure) indistinguishability obfuscator and one-way functions. Then the End-of-the-Line problem is hard on average for polynomial-time algorithms; consequently $\mathsf{PPAD}$ contains problems that are hard on average, and computing a Nash equilibrium of a two-player game in normal form is cryptographically hard.

## Proof sketch

Construct an End-of-the-Line instance whose line consists of signed counter values $\sigma_i=F(K,i)$ for a puncturable PRF; obfuscated successor and predecessor circuits check signatures. Punctured programming at the end of the line, together with a hybrid argument along the line, shows that finding the end or another unbalanced vertex requires forging a PRF value.

## Depends on

- [Indistinguishability and virtual black-box obfuscation](../../../program-obfuscation/indistinguishability-and-virtual-black-box.md)

## Proof depends on

- [Punctured programming: swapping a program for a functionally equivalent punctured one](punctured-programming-hybrid.md)
- [Complexity leveraging for exponentially many hybrids](../compact-functional-encryption-to-obfuscation/io-complexity-leveraging.md)

## Sources

- Nir Bitansky, Omer Paneth, Alon Rosen, "On the Cryptographic Hardness of Finding a Nash Equilibrium", FOCS (2015).
