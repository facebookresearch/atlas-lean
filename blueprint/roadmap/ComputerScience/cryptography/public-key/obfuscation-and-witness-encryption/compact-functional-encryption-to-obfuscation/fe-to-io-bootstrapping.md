# Indistinguishability obfuscation from sub-exponentially secure compact functional encryption

Assume a public-key functional encryption scheme for all polynomial-size circuits that is single-key, selectively secure with sub-exponential advantage, and weakly compact. Then there exists an indistinguishability obfuscator for all polynomial-size circuits ($\mathsf{P}/\mathsf{poly}$).

## Proof sketch

Obfuscate $C:\{0,1\}^{n}\to\{0,1\}$ by a binary tree of depth $n$: at level $i$ a functional key computes the map that, on an encryption of a prefix $x_1\cdots x_i$ (with fresh seed), outputs encryptions of both one-bit extensions under the next level's key, and the last level outputs $C(x)$. Compactness keeps ciphertext sizes from compounding along the depth. Security is proven by a hybrid over all $2^{n}$ inputs, each step changing one path, which incurs a $2^{n}$ loss absorbed by sub-exponential security with $\lambda$ chosen polynomially larger than $n$.

## Depends on

- [Single-key weakly compact public-key functional encryption](weakly-compact-fe.md)
- [Indistinguishability and virtual black-box obfuscation](../../../program-obfuscation/indistinguishability-and-virtual-black-box.md)

## Sources

- Prabhanjan Ananth, Abhishek Jain, "Indistinguishability Obfuscation from Compact Functional Encryption", CRYPTO (2015), IACR ePrint 2015/173.
- Nir Bitansky, Vinod Vaikuntanathan, "Indistinguishability Obfuscation from Functional Encryption", FOCS (2015), IACR ePrint 2015/163.
