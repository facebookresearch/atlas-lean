# CKKS encoding via the canonical embedding

Let $N$ be a power of two, $R=\mathbb{Z}[X]/(X^{N}+1)$ and $\zeta=e^{\pi i/N}$. The *canonical embedding* restricted to half the roots is $\tau:\mathbb{R}[X]/(X^{N}+1)\to\mathbb{C}^{N/2}$, $\tau(m)=(m(\zeta^{5^{j}}))_{0\le j< N/2}$, an isomorphism of $\mathbb{R}$-algebras onto $\mathbb{C}^{N/2}$ (the other roots give complex conjugates). For a scaling factor $\Delta>0$, the encoding of $\mathbf{z}\in\mathbb{C}^{N/2}$ is $\mathrm{Ecd}(\mathbf{z})=\lfloor\Delta\cdot\tau^{-1}(\mathbf{z})\rceil\in R$ (coefficientwise rounding), and the decoding of $m\in R$ is $\mathrm{Dcd}(m)=\Delta^{-1}\tau(m)$. The *canonical norm* is $\|m\|^{\mathrm{can}}=\|\tau(m)\|_\infty$, which satisfies $\|m\|^{\mathrm{can}}\le\|m\|_1$ and $\|mm'\|^{\mathrm{can}}\le\|m\|^{\mathrm{can}}\|m'\|^{\mathrm{can}}$.

## Depends on

- [BGV and BFV ring ciphertexts](../leveled-packed-fhe-bgv-and-bfv/bgv-bfv-ciphertexts.md)

## Sources

- Jung Hee Cheon, Andrey Kim, Miran Kim, Yongsoo Song, "Homomorphic Encryption for Arithmetic of Approximate Numbers", ASIACRYPT (2017), IACR ePrint 2016/421.
