# Noise of the TRGSW–TRLWE external product

For a TRGSW sample $\mathbf{A}$ of $\mu_A\in\mathbb{Z}_N[X]$ with error variance $\vartheta_A$ and a TRLWE sample $\mathbf{b}$ of $\mu_b$ with error variance $\vartheta_b$, define the external product $\mathbf{A}\boxdot\mathbf{b}=\mathrm{Dec}_{\mathbf{H},\beta,\epsilon}(\mathbf{b})\cdot\mathbf{A}$. Then $\mathbf{A}\boxdot\mathbf{b}$ is a TRLWE sample of $\mu_A\cdot\mu_b$ whose error variance (under the usual independence heuristic) satisfies

$$
\mathrm{Var}\le(k+1)\ell N\beta^{2}\vartheta_A+(1+kN)\|\mu_A\|_2^{2}\epsilon^{2}+\|\mu_A\|_2^{2}\vartheta_b.
$$

In particular, when $\mu_A$ is a monomial $\pm X^{j}$ or a bit, the noise grows additively in $\vartheta_b$, which is what makes blind rotation noise-efficient.

## Proof sketch

Write $\mathbf{u}=\mathrm{Dec}(\mathbf{b})$ with $\mathbf{u}\mathbf{H}=\mathbf{b}+\boldsymbol{\epsilon}'$. Then $\mathbf{u}\mathbf{A}=\mathbf{u}\mathbf{Z}+\mu_A(\mathbf{b}+\boldsymbol{\epsilon}')$. The first term is a combination of TRLWE samples of $0$ with small integer coefficients, contributing error variance at most $(k+1)\ell N\beta^{2}\vartheta_A$; the second encrypts $\mu_A\mu_b$ with error $\mu_A e_b$ plus the rounding term $\mu_A\langle\boldsymbol{\epsilon}',(\mathbf{s},-1)\rangle$, of variance at most $(1+kN)\|\mu_A\|_2^{2}\epsilon^{2}$.

## Depends on

- [TRGSW samples and the gadget decomposition](trgsw-samples.md)
- [TLWE and TRLWE samples over the real torus](tlwe-samples.md)

## Sources

- Ilaria Chillotti, Nicolas Gama, Mariya Georgieva, Malika Izabachène, "TFHE: Fast Fully Homomorphic Encryption over the Torus", Journal of Cryptology (2020), IACR ePrint 2018/421.
