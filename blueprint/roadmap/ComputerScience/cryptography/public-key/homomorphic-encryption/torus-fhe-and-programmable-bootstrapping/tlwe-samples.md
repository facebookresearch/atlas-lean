# TLWE and TRLWE samples over the real torus

Let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ be the real torus, a $\mathbb{Z}$-module, and $\mathbb{T}_N[X]=\mathbb{T}[X]/(X^{N}+1)$, a module over $\mathbb{Z}_N[X]=\mathbb{Z}[X]/(X^{N}+1)$, for $N$ a power of two. For a binary secret $\mathbf{s}\in\{0,1\}^{n}$, a *TLWE sample* of a message $\mu\in\mathbb{T}$ is $(\mathbf{a},b)\in\mathbb{T}^{n+1}$ with $\mathbf{a}$ uniform and $b=\langle\mathbf{a},\mathbf{s}\rangle+\mu+e$ for Gaussian error $e$ of variance $\vartheta$; its *phase* is $\varphi_{\mathbf{s}}(\mathbf{a},b)=b-\langle\mathbf{a},\mathbf{s}\rangle$. A *TRLWE sample* of $\mu\in\mathbb{T}_N[X]$ under a secret $\mathbf{s}\in\mathbb{B}_N[X]^{k}$ (binary-coefficient polynomials) is $(\mathbf{a},b)\in\mathbb{T}_N[X]^{k+1}$ with $b=\langle\mathbf{a},\mathbf{s}\rangle+\mu+e$. Decryption rounds the phase to the nearest element of a discrete message space such as $\frac{1}{2^{p}}\mathbb{Z}/\mathbb{Z}$.

## Depends on

- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Sources

- Ilaria Chillotti, Nicolas Gama, Mariya Georgieva, Malika Izabachène, "TFHE: Fast Fully Homomorphic Encryption over the Torus", Journal of Cryptology (2020), IACR ePrint 2018/421.
