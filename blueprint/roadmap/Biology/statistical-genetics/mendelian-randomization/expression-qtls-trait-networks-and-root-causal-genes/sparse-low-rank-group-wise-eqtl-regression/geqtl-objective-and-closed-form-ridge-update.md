# geQTL objective and closed-form ridge update

Let $X \in \mathbb{R}^{K\times H}$ be standardized genotypes of $K$ SNPs and $Z \in \mathbb{R}^{N \times H}$ standardized expression of $N$ genes over $H$ samples. With latent group variables $y = Ax + \varepsilon_1$ ($A \in \mathbb{R}^{M\times K}$, $M \ll \min(K,N)$) and $z = By + Cx + \varepsilon_2$, the **geQTL** estimator solves

$$\min_{A,B,C,L}\; \|Z - L - (BA + C)X\|_F^2 + \rho\|L\|_* + \alpha\|A\|_1 + \beta\|B\|_1 + \gamma\|C\|_1,$$

where $L \in \mathbb{R}^{N\times H}$ is a low-rank confounder matrix penalized by the nuclear norm, $BA$ carries group-wise associations through $M$ latent factors and $C$ carries individual SNP–gene associations (Cheng et al. 2016, Eqs. 6–12).

**Confounder update.** For fixed $A, B, C$, the $L$-step is singular value soft-thresholding: the minimizer of $\tfrac12\|O - S\|_F^2 + \lambda\|S\|_*$ is $S = U\,\mathrm{diag}((d_i - \lambda)_+)\,V^\top$ where $O = UDV^\top$ is an SVD (Lemma 1), applied with $O = Z - (BA + C)X$.

**Ridge variant.** If the $\ell_1$ penalty on $C$ is replaced by $\gamma\|C\|_2^2$ and $C_{ij}$ is allowed to be nonzero only where a 0/1 screening matrix has $R_{ij} = 1$, then, with $D = Z - L - BAX$ and $P_i$ the 0/1 matrix selecting the SNPs allowed for gene $i$, the $i$th row of $C$ has the closed form

$$c_i = d_i X^\top P_i\left(P_i^\top X X^\top P_i + \gamma I\right)^{-1} P_i^\top$$

(Theorem 1, geQTL-ridge), where $d_i$ is the $i$th row of $D$.

## Depends on

- [Group-wise eQTL latent model and fast covariance inversion](../group-wise-eqtl-latent-variable-model/group-wise-eqtl-latent-model-and-fast-covariance-inversion.md)

## Expansion

Fixing the other blocks, each row of $C$ solves an independent ridge regression of $d_i$ on the rows of $X$ selected by $P_i$; the normal equations give the displayed formula, and $P_i^\top$ embeds the solution back into $\mathbb{R}^K$ with zeros elsewhere. The nuclear-norm step is the proximal operator of $\lambda\|\cdot\|_*$, which acts on singular values exactly as soft-thresholding acts on scalars. Restricting $C$ to a screened support is what removes the main computational bottleneck, since $M \ll \min(K,N)$ makes the $A$ and $B$ updates cheap.

## Sources

- W. Cheng, Y. Shi, X. Zhang and W. Wang, *Sparse regression models for unraveling group and individual associations in eQTL mapping*, BMC Bioinformatics 17 (2016), 136, Eqs. (3)–(14), Lemma 1 and Theorem 1. <https://doi.org/10.1186/s12859-016-0986-9> (PMCID: PMC4802846)
