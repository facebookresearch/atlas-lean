# Network deconvolution closed form

Let $G_{\mathrm{dir}} \in \mathbb{R}^{p \times p}$ be a matrix of direct dependencies among $p$ variables (genes, residues) with spectral radius $\rho(G_{\mathrm{dir}}) < 1$. The **network convolution model** assumes that an indirect path of length $k$ contributes the product of its direct edge weights, and that observed weights are the sum over all paths:

$$G_{\mathrm{obs}} = G_{\mathrm{dir}} + G_{\mathrm{dir}}^2 + G_{\mathrm{dir}}^3 + \cdots .$$

**Theorem.** Under this model the series converges and

$$G_{\mathrm{obs}} = G_{\mathrm{dir}} (I - G_{\mathrm{dir}})^{-1}, \qquad G_{\mathrm{dir}} = G_{\mathrm{obs}} (I + G_{\mathrm{obs}})^{-1},$$

where $I + G_{\mathrm{obs}}$ is invertible. If $G_{\mathrm{obs}} = U \Sigma_{\mathrm{obs}} U^{-1}$ is diagonalizable with eigenvalues $\lambda^{\mathrm{obs}}_i$, then $G_{\mathrm{dir}} = U \Sigma_{\mathrm{dir}} U^{-1}$ with

$$\lambda^{\mathrm{dir}}_i = \frac{\lambda^{\mathrm{obs}}_i}{1 + \lambda^{\mathrm{obs}}_i}, \qquad \lambda^{\mathrm{obs}}_i = \frac{\lambda^{\mathrm{dir}}_i}{1 - \lambda^{\mathrm{dir}}_i}.$$

For a symmetric observed matrix (correlation or mutual information), $U$ can be taken orthogonal, and a real eigenvalue $\lambda^{\mathrm{dir}} \in (-1, 1)$ corresponds exactly to $\lambda^{\mathrm{obs}} > -\tfrac12$.

## Expansion

Since $\rho(G_{\mathrm{dir}}) < 1$, the Neumann series $\sum_{k \ge 0} G_{\mathrm{dir}}^k$ converges to $(I - G_{\mathrm{dir}})^{-1}$, and multiplying by $G_{\mathrm{dir}}$ (which commutes with it) gives the first identity. Then $I + G_{\mathrm{obs}} = (I - G_{\mathrm{dir}})^{-1}$, which is invertible, so $G_{\mathrm{obs}}(I + G_{\mathrm{obs}})^{-1} = G_{\mathrm{dir}} (I - G_{\mathrm{dir}})^{-1} (I - G_{\mathrm{dir}}) = G_{\mathrm{dir}}$. Every polynomial or rational function of a diagonalizable matrix acts on its eigenvalues with the same eigenvectors, giving the scalar map $\lambda \mapsto \lambda/(1+\lambda)$, a nonlinear filter that shrinks large positive eigenvalues inflated by indirect flow. The map $x \mapsto x/(1-x)$ is an increasing bijection from $(-1,1)$ onto $(-\tfrac12, \infty)$. In practice the observed matrix has its diagonal zeroed and is linearly rescaled so that the recovered direct matrix has spectral radius below one; Feizi et al. also give a conjugate-gradient formulation for non-diagonalizable inputs and a noisy-observation variant.

## Sources

- S. Feizi, D. Marbach, M. Médard and M. Kellis, "Network deconvolution as a general method to distinguish direct dependencies in networks", Nature Biotechnology 31 (2013), Methods "Network deconvolution" (Steps 1–2), <https://doi.org/10.1038/nbt.2635>, PMCID PMC3773370.
