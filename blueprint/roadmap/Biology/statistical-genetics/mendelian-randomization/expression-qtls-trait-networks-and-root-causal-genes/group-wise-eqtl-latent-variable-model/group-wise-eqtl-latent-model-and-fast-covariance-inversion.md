# Group-wise eQTL latent model and fast covariance inversion

Let $x \in \mathbb{R}^K$ be genotypes at $K$ SNPs, $y \in \mathbb{R}^M$ hidden group variables and $z \in \mathbb{R}^N$ expression levels of $N$ genes, with confounders $s \sim \mathcal N(0, I_H)$. The model is

$$y = Ax + \varepsilon_1, \qquad z = By + Cx + Ws + \mu_B + \varepsilon_2,$$

with $\varepsilon_1 \sim \mathcal N(0, \sigma_1^2 I_M)$, $\varepsilon_2 \sim \mathcal N(0, \sigma_2^2 I_N)$, and independent Laplace priors on the entries of $A$ (SNP-to-group), $B$ (group-to-gene) and $C$ (direct SNP-to-gene) (Cheng et al. 2015, Eqs. 4–5). Marginalizing $y$ and $s$,

$$z \mid x \sim \mathcal N\!\left(BAx + Cx + \mu_B,\; \Sigma\right), \qquad \Sigma = \sigma_1^2 BB^\top + WW^\top + \sigma_2^2 I_N,$$

and the MAP estimate minimizes the Gaussian negative log-likelihood plus $D(\lambda\|A\|_1 + \gamma\|B\|_1 + \alpha\|C\|_1)$ over $D$ samples, with $\mu_B$ profiled out as the mean residual (Eqs. 8–11). Nonzero blocks of $A$ and $B$ identify associations between SNP sets and gene sets through a shared hidden variable.

**Theorem (fast inverse).** For $B \in \mathbb{R}^{N\times M}$, $W \in \mathbb{R}^{N \times H}$ and $\Sigma = \sigma_2^2 I_N + \sigma_1^2 BB^\top + WW^\top$,

$$\Sigma^{-1} = T - TW S^{-1} W^\top T, \qquad S = I_H + W^\top T W, \qquad T = \sigma_2^{-2}\left(I_N - \sigma_1^2 B\left(\sigma_2^2 I_M + \sigma_1^2 B^\top B\right)^{-1} B^\top\right)$$

(Cheng et al. 2015, Theorem 1). Since $M, H \ll N$, this replaces the $O(N^3)$ inversion by inversions of size $M$ and $H$.

## Depends on

- [Laplace distribution](../../../../../Probability/distributions/continuous/laplace-distribution/laplace-measure.md)

## Expansion

Both identities are applications of the Sherman–Morrison–Woodbury formula. First, $(\sigma_2^2 I_N + B(\sigma_1^2 I_M)B^\top)^{-1} = \sigma_2^{-2}[I_N - B(\sigma_2^2\sigma_1^{-2} I_M + B^\top B)^{-1}B^\top]$, which equals $T$. Second, $\Sigma = T^{-1} + WW^\top$, and Woodbury with the identity core gives $T - TW(I_H + W^\top T W)^{-1}W^\top T$. Given $\Sigma$'s eigenvalues $\lambda_s$ of $\sigma_1^2 BB^\top + WW^\top$, the update of $\sigma_2^2$ is a one-dimensional problem (Eq. 13).

## Sources

- W. Cheng, Y. Shi, X. Zhang and W. Wang, *Fast and robust group-wise eQTL mapping using sparse graphical models*, BMC Bioinformatics 16 (2015), 2, Eqs. (4)–(13) and Theorem 1. <https://doi.org/10.1186/s12859-014-0421-z> (PMCID: PMC4387667)
