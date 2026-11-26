# TRGSW samples and the gadget decomposition

Fix a base $B_g$ and a number of levels $\ell$, and let $\mathbf{H}\in\mathbb{T}_N[X]^{(k+1)\ell\times(k+1)}$ be the gadget matrix whose block for each column $j$ contains the entries $1/B_g,\dots,1/B_g^{\ell}$. A *TRGSW sample* of $\mu\in\mathbb{Z}_N[X]$ is $\mathbf{C}=\mathbf{Z}+\mu\cdot\mathbf{H}$, where $\mathbf{Z}$ consists of $(k+1)\ell$ independent TRLWE samples of $0$. The *gadget decomposition* $\mathrm{Dec}_{\mathbf{H},\beta,\epsilon}(\mathbf{v})$ of $\mathbf{v}\in\mathbb{T}_N[X]^{k+1}$ returns $\mathbf{u}\in\mathbb{Z}_N[X]^{(k+1)\ell}$ with $\|\mathbf{u}\|_\infty\le\beta=B_g/2$ and $\|\mathbf{u}\mathbf{H}-\mathbf{v}\|_\infty\le\epsilon=1/(2B_g^{\ell})$.

## Depends on

- [TLWE and TRLWE samples over the real torus](tlwe-samples.md)

## Sources

- Ilaria Chillotti, Nicolas Gama, Mariya Georgieva, Malika Izabachène, "TFHE: Fast Fully Homomorphic Encryption over the Torus", Journal of Cryptology (2020), IACR ePrint 2018/421.
- Craig Gentry, Amit Sahai, Brent Waters, "Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based", CRYPTO (2013).
