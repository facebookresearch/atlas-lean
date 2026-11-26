# Orthogonal extension by least squares from Kam autocorrelations

In single-particle cryo-electron microscopy, let $\Phi_A:\mathbb{R}^3\to\mathbb{R}$ be the unknown electron scattering density of a molecule and expand its Fourier transform in real spherical harmonics and a truncated radial basis of normalised spherical Bessel functions $j_{ls}$:

$$
\mathcal{F}(\Phi_A)(k,\theta,\varphi)=\sum_{l=0}^{L}\sum_{m=-l}^{l}A_{lm}(k)Y_l^m(\theta,\varphi),\qquad A_{lm}(k)=\sum_{s=1}^{S_l}a_{lms}\,j_{ls}(k).
$$

**Kam's autocorrelation matrices.** For projection images with viewing directions uniformly distributed on the sphere, the matrices

$$
C_l(k_1,k_2)=\sum_{m=-l}^{l}A_{lm}(k_1)\overline{A_{lm}(k_2)}
$$

are identifiable from the covariance of the 2D images (even noisy ones, given enough images). In matrix form $\mathbf C_l=\mathbf A_l\mathbf A_l^*$ with $\mathbf A_l\in\mathbb{C}^{S_l\times(2l+1)}$, $\mathbf A_l(s,m)=a_{lms}$, so $\operatorname{rank}\mathbf C_l\le2l+1$. Since $\Phi_A$ is real, $\mathbf A_l$ is real for even $l$ and purely imaginary for odd $l$; hence any factor $\mathbf F_l$ with $\mathbf F_l\mathbf F_l^*=\mathbf C_l$ determines $\mathbf A_l=\mathbf F_l\mathbf O_l$ only up to an orthogonal matrix $\mathbf O_l\in\mathrm{O}(2l+1)$ (orthogonal retrieval problem).

**Least-squares orthogonal extension.** Given the coefficient matrix $\mathbf B_l$ of a known homologous structure ($\mathbf A_l\approx\mathbf B_l$), the Procrustes problem $\min_{\mathbf O\in\mathrm O(2l+1)}\|\mathbf F_l\mathbf O-\mathbf B_l\|_F$ has the closed-form solution $\mathbf O_l=\mathbf V_l\mathbf U_l^{T}$, where $\mathbf B_l^*\mathbf F_l=\mathbf U_l\boldsymbol\Sigma_l\mathbf V_l^{T}$ is a singular value decomposition, yielding the estimator

$$
\hat{\mathbf A}_{l,\mathrm{LS}}=\mathbf F_l\mathbf V_l\mathbf U_l^{T}.
$$

The radial truncation $S_l$ is the largest $s$ with $R_{l,s+1}\le2\pi cR$, where $R_{l,s}$ is the $s$-th positive zero of $j_l$, $c$ the image bandlimit and $R$ the support radius; $L$ is the largest $l$ with $S_l\ge1$.

## Expansion

Rotational averaging over uniformly distributed views destroys the phases within each angular-frequency shell $l$ but preserves the Gram matrices $\mathbf C_l$, which is Kam's theory. The missing information is one orthogonal matrix per $l$; when $S_l>2l+1$ this is fewer unknowns than $\mathbf A_l$ itself, and a homologous structure pins it down, generalising molecular replacement from X-ray crystallography. For large $l$ where $S_l<2l+1$, estimating $\mathbf O_l$ is pointless, but the same least-squares formula still gives the $\mathbf A_l$ closest to $\mathbf B_l$ consistent with $\mathbf C_l$.

## Sources

- T. Bhamre, T. Zhang, A. Singer, "Anisotropic twicing for single particle reconstruction using autocorrelation analysis", Sections 2–3 (Algorithm 1). <https://doi.org/10.48550/arXiv.1704.07969>
