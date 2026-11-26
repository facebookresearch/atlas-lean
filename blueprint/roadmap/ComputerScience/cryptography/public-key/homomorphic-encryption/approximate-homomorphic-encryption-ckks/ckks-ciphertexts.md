# CKKS ciphertexts and approximate decryption

Fix a chain of moduli $q_\ell=p^{\ell}q_0$ (or products of RNS primes $q_\ell=\prod_{j\le\ell}p_j$) for levels $0\le\ell\le L$, a secret $s\in R$ of Hamming weight $h$, and a Gaussian error distribution. A *CKKS ciphertext* at level $\ell$ is $\mathbf{c}=(b,a)\in R_{q_\ell}^{2}$, and it *encrypts $m\in R$ with error bound $B$* if $b+as\equiv m+e\pmod{q_\ell}$ with $\|e\|^{\mathrm{can}}\le B$. Decryption returns $\langle\mathbf{c},(1,s)\rangle\bmod q_\ell=m+e$, an approximation of $m$: the error is not removed but becomes part of the low-order bits of the decoded complex values.

## Depends on

- [CKKS encoding via the canonical embedding](canonical-embedding-encoding.md)
- [Hardness of Ring-LWE from worst-case problems on ideal lattices](../../isogeny-and-lattice-foundations/worst-case-to-average-case-lattice-reductions/ring-lwe-hardness.md)

## Sources

- Jung Hee Cheon, Andrey Kim, Miran Kim, Yongsoo Song, "Homomorphic Encryption for Arithmetic of Approximate Numbers", ASIACRYPT (2017), IACR ePrint 2016/421.
