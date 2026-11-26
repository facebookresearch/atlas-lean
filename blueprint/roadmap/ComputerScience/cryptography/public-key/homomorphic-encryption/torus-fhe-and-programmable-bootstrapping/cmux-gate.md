# The homomorphic multiplexer CMux

For a TRGSW sample $\mathbf{C}$ of a bit $b\in\{0,1\}$ and TRLWE samples $\mathbf{d}_0,\mathbf{d}_1$ of $\mu_0,\mu_1$, the sample $\mathrm{CMux}(\mathbf{C},\mathbf{d}_1,\mathbf{d}_0)=\mathbf{C}\boxdot(\mathbf{d}_1-\mathbf{d}_0)+\mathbf{d}_0$ is a TRLWE sample of $\mu_b$, with error variance at most $\max(\vartheta_0,\vartheta_1)+(k+1)\ell N\beta^{2}\vartheta_C+(1+kN)\epsilon^{2}$.

## Proof sketch

By the external product lemma $\mathbf{C}\boxdot(\mathbf{d}_1-\mathbf{d}_0)$ encrypts $b(\mu_1-\mu_0)$ with $\|\mu_A\|_2=b\le 1$; adding $\mathbf{d}_0$ gives $\mu_b$. When $b=1$ the errors of $\mathbf{d}_0$ cancel up to the external product terms, and when $b=0$ only $\mathbf{d}_0$'s error remains plus the external product contribution.

## Depends on

- [Noise of the TRGSW–TRLWE external product](external-product-noise.md)
- [TLWE and TRLWE samples over the real torus](tlwe-samples.md)
- [TRGSW samples and the gadget decomposition](trgsw-samples.md)

## Sources

- Ilaria Chillotti, Nicolas Gama, Mariya Georgieva, Malika Izabachène, "TFHE: Fast Fully Homomorphic Encryption over the Torus", Journal of Cryptology (2020), IACR ePrint 2018/421.
