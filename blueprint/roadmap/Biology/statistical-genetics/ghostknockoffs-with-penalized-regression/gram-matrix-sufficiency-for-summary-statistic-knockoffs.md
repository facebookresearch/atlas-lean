# Gram-matrix sufficiency for summary-statistic knockoffs

**Setting.** Rows of the genotype (covariate) matrix $\mathbf X\in\mathbb R^{n\times p}$ are i.i.d. $\mathcal N(\mathbf 0,\boldsymbol\Sigma)$ with $\boldsymbol\Sigma$ known (for example from a linkage-disequilibrium reference panel), $\mathbf Y\in\mathbb R^n$ is the trait vector, and the hypotheses are the conditional independences $H_0^j: X_j\perp Y\mid X_{-j}$. The **Gaussian knockoff sampler** $\mathcal G(\mathbf X,\boldsymbol\Sigma)$ outputs

$$
\widetilde{\mathbf X}=\mathbf X\mathbf P+\mathbf E\mathbf V^{1/2},\qquad \mathbf P=\mathbf I-\boldsymbol\Sigma^{-1}\mathbf D,\quad \mathbf V=2\mathbf D-\mathbf D\boldsymbol\Sigma^{-1}\mathbf D,
$$

where $\mathbf D=\operatorname{diag}(\mathbf s)$ is chosen so that $\mathbf V\succeq 0$, and $\mathbf E$ has i.i.d. standard normal entries independent of $(\mathbf X,\mathbf Y)$. Let $\mathcal T(\mathbf X,\widetilde{\mathbf X},\mathbf Y)=[\mathbf X,\widetilde{\mathbf X},\mathbf Y]^\top[\mathbf X,\widetilde{\mathbf X},\mathbf Y]$ be the joint Gram matrix.

**Proposition (Gram-matrix sufficiency).** Let $\check{\mathbf X}\in\mathbb R^{n\times p}$ and $\check{\mathbf Y}\in\mathbb R^n$ be any matrices with the same Gram matrix as the data, $[\check{\mathbf X}\ \check{\mathbf Y}]^\top[\check{\mathbf X}\ \check{\mathbf Y}]=[\mathbf X\ \mathbf Y]^\top[\mathbf X\ \mathbf Y]$ (for example obtained by an eigen- or Cholesky decomposition of that Gram matrix). With $\widetilde{\mathbf X}=\mathcal G(\mathbf X,\boldsymbol\Sigma)$ and $\widetilde{\check{\mathbf X}}=\mathcal G(\check{\mathbf X},\boldsymbol\Sigma)$,

$$
\mathcal T(\mathbf X,\widetilde{\mathbf X},\mathbf Y)\mid\mathbf X,\mathbf Y\ \stackrel{d}{=}\ \mathcal T(\check{\mathbf X},\widetilde{\check{\mathbf X}},\check{\mathbf Y})\mid\mathbf X,\mathbf Y .
$$

**Corollary (equivalent selection from summary statistics).** Let $\mathbf W=\mathbf f(\mathcal T(\mathbf X,\widetilde{\mathbf X},\mathbf Y),\mathbf U)$ be any feature-importance statistic that is a deterministic function of the joint Gram matrix and an independent randomization $\mathbf U$, and let $\widehat{\mathbf W}$ be the same function evaluated on the surrogate data. The knockoff filter (select $\{j:W_j\ge T\}$ with $T=\min\{t>0:(1+\#\{j:W_j\le -t\})/(\#\{j:W_j\ge t\}\vee 1)\le q\}$) applied to $\mathbf W$ and to $\widehat{\mathbf W}$ gives rejection sets with the same conditional law given $(\mathbf X,\mathbf Y)$. Hence, whenever $\mathbf W$ has the flip-sign property (swapping $\mathbf X_j$ with $\widetilde{\mathbf X}_j$ negates $W_j$), both procedures control the false discovery rate at level $q$. This covers the Lasso coefficient difference $W_j=|\hat\beta_j(\lambda)|-|\hat\beta_{j+p}(\lambda)|$ at a fixed penalty, the square-root Lasso, the Lasso-max statistic, ridge and elastic net, all of which depend on the data only through $\mathcal T$. So the inputs $\mathbf X^\top\mathbf X$, $\mathbf X^\top\mathbf Y$, $\|\mathbf Y\|_2^2$, $\boldsymbol\Sigma$ and $n$ suffice for FDR-controlled penalized-regression knockoffs; individual-level genotypes are never needed.

## Expansion

Write $\mathbf M=[\mathbf X\ \mathbf Y]$. Every block of $\mathcal T$ is a polynomial in $\mathbf M^\top\mathbf M$, $\mathbf E^\top\mathbf M$ and $\mathbf E^\top\mathbf E$; for instance $\widetilde{\mathbf X}^\top\mathbf Y=\mathbf P^\top\mathbf X^\top\mathbf Y+\mathbf V^{1/2}\mathbf E^\top\mathbf Y$. Two $n$-row matrices with the same Gram matrix differ by an orthogonal $n\times n$ matrix, $\check{\mathbf M}=\mathbf Q\mathbf M$, and the Gaussian matrix $\mathbf E$ is rotation invariant ($\mathbf Q^\top\mathbf E\stackrel d=\mathbf E$), so $(\mathbf E^\top\check{\mathbf M},\mathbf E^\top\mathbf E)\stackrel d=(\mathbf E^\top\mathbf M,\mathbf E^\top\mathbf E)$, which gives the proposition. The corollary follows because the knockoff filter is a deterministic function of $\mathbf W$, and the individual-level procedure controls the FDR by the model-X knockoff theorem. A practical consequence is that cross-validation cannot be used directly (it needs rows), which is why tuning in this setting uses rules computable from the Gram matrix.

## Sources

- Z. Chen, Z. He, B. B. Chu, J. Gu, "Controlled Variable Selection from Summary Statistics Only? A Solution via GhostKnockoffs and Penalized Regression" (2024), Section 3.2, Proposition 1 and Corollary 1. <https://doi.org/10.48550/arXiv.2402.12724>
