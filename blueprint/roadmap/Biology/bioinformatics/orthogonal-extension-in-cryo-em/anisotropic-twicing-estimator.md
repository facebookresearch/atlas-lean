# Anisotropic twicing estimator

Let $\mathbf C=\mathbf A\mathbf A^*\in\mathbb{C}^{D\times D}$ be a known Gram matrix with spectral decomposition $\mathbf C=\mathbf U\operatorname{diag}(\lambda_1,\dots,\lambda_D)\mathbf U^*$, and let $\mathbf B$ be a known reference with $\mathbf A-\mathbf B$ fixed (a homologous structure). Model the unknown as $\mathbf A=\mathbf F\mathbf V$, where $\mathbf F\mathbf F^*=\mathbf C$ and $\mathbf V$ is Haar-distributed on the orthogonal group (real case) or unitary group (complex case). Let $\hat{\mathbf A}_{\mathrm{LS}}=\mathbf F\mathbf V_0\mathbf U_0^*$ be the least-squares (Procrustes) estimator, where $\mathbf B^*\mathbf F=\mathbf U_0\boldsymbol\Sigma_0\mathbf V_0^*$.

**Theorem (bias of least squares, $N=D$).**

$$
\mathbb{E}\big[\mathbf A-\hat{\mathbf A}_{\mathrm{LS}}\big]=\mathbf U\mathbf T\mathbf U^*(\mathbf A-\mathbf B)+o(\|\mathbf A-\mathbf B\|_F),
$$

where $\mathbf T$ is diagonal with

$$
T_{ii}=\begin{cases}\dfrac1D\Big[-\dfrac12+\displaystyle\sum_{j=1}^{D}\frac{\lambda_i^2}{\lambda_i^2+\lambda_j^2}\Big], & \mathbf A,\mathbf C\ \text{real},\\[2ex] \dfrac1D\displaystyle\sum_{j=1}^{D}\frac{\lambda_i^2}{\lambda_i^2+\lambda_j^2}, & \mathbf A,\mathbf C\ \text{complex}.\end{cases}
$$

Consequently the **anisotropic twicing** estimator

$$
\hat{\mathbf A}_{\mathrm{AT}}=\mathbf B+\mathbf U\mathbf W\mathbf U^*\big(\hat{\mathbf A}_{\mathrm{LS}}-\mathbf B\big),\qquad \mathbf W=(\mathbf I-\mathbf T)^{-1},
$$

is unbiased to first order in $\|\mathbf A-\mathbf B\|_F$. In the scalar case $D=1$ (complex), $\mathbf T=\tfrac12$, $\mathbf W=2$ and $\hat{\mathbf A}_{\mathrm{AT}}=2\hat{\mathbf A}_{\mathrm{LS}}-\mathbf B$, the classical twicing estimator of X-ray crystallography.

## Depends on

- [Orthogonal extension by least squares from Kam autocorrelations](orthogonal-extension-by-least-squares-from-kam-autocorrelations.md)

## Expansion

The least-squares estimator is pulled toward the reference: its error is a shrunken copy of $\mathbf A-\mathbf B$. Expanding the Procrustes solution to first order in the perturbation and averaging over the Haar measure, the shrinkage acts diagonally in the eigenbasis of $\mathbf C$ with factors depending only on the eigenvalue ratios, so it is anisotropic. Inverting the first-order bias map removes the model bias that the homologous reference imprints on the reconstruction, at the cost of higher variance; the paper also gives a family of estimators interpolating between the two, and extends the construction to $N\ne D$. Applied shell by shell to the cryo-EM coefficient matrices, it gives an initial 3D model with less reference bias, tested on synthetic and experimental TRPV1 data.

## Sources

- T. Bhamre, T. Zhang, A. Singer, "Anisotropic twicing for single particle reconstruction using autocorrelation analysis", Section 4 (Theorem 1) and Appendix. <https://doi.org/10.48550/arXiv.1704.07969>
