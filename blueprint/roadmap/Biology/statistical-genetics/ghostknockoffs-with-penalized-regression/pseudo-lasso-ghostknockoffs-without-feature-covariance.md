# Pseudo-lasso GhostKnockoffs without the feature Gram matrix

**Setting.** As for the Gaussian knockoff sampler $\widetilde{\mathbf X}=\mathbf X\mathbf P+\mathbf E\mathbf V^{1/2}$ with $\mathbf P=\mathbf I-\boldsymbol\Sigma^{-1}\mathbf D$, $\mathbf V=2\mathbf D-\mathbf D\boldsymbol\Sigma^{-1}\mathbf D$, $\mathbf D=\operatorname{diag}(\mathbf s)$, rows of $\mathbf X$ i.i.d. $\mathcal N(\mathbf 0,\boldsymbol\Sigma)$ with $\boldsymbol\Sigma$ known. Now only the marginal association statistics $\mathbf X^\top\mathbf Y$, the scalar $\|\mathbf Y\|_2^2$, the sample size $n$ and $\boldsymbol\Sigma$ are available (typical of published GWAS summary statistics); the empirical feature covariance $\mathbf X^\top\mathbf X$ is not.

**Proposition (knockoff $Z$-score identity).** Let $\mathbf Z\sim\mathcal N(\mathbf 0,\mathbf V)$ be independent of $(\mathbf X,\mathbf Y)$. Then

$$
\widetilde{\mathbf X}^\top\mathbf Y\mid\mathbf X,\mathbf Y\ \stackrel d=\ \mathbf P^\top\mathbf X^\top\mathbf Y+\|\mathbf Y\|_2\,\mathbf Z\mid\mathbf X,\mathbf Y .
$$

Consequently, for any statistic $\mathbf W=\mathbf g(\|\mathbf Y\|_2^2,\mathbf X^\top\mathbf Y,\widetilde{\mathbf X}^\top\mathbf Y,\mathbf U)$ with $\mathbf U$ an independent randomization, the statistic $\widehat{\mathbf W}$ obtained by substituting $\mathbf P^\top\mathbf X^\top\mathbf Y+\|\mathbf Y\|_2\mathbf Z$ for $\widetilde{\mathbf X}^\top\mathbf Y$ yields knockoff-filter rejection sets with the same conditional law; if $\mathbf W$ has the flip-sign property both control the FDR at level $q$. The marginal-correlation statistic $W_j=|(\mathbf X^\top\mathbf Y)_j|-|(\widetilde{\mathbf X}^\top\mathbf Y)_j|$ (the original GhostKnockoffs) is the special case.

**Pseudo-lasso statistic.** Fix $\lambda>0$ and $c\ge 0$ and solve

$$
\hat{\boldsymbol\beta}\in\arg\min_{\boldsymbol\beta\in\mathbb R^{2p}}\ \tfrac12\boldsymbol\beta^\top\mathbf C\boldsymbol\beta-\tfrac1n\boldsymbol\beta^\top\begin{bmatrix}\mathbf X^\top\mathbf Y\\ \mathbf P^\top\mathbf X^\top\mathbf Y+\|\mathbf Y\|_2\mathbf Z\end{bmatrix}+\lambda\|\boldsymbol\beta\|_1,\qquad \mathbf C=\begin{bmatrix}\boldsymbol\Sigma+c\mathbf I&\boldsymbol\Sigma-\mathbf D\\ \boldsymbol\Sigma-\mathbf D&\boldsymbol\Sigma+c\mathbf I\end{bmatrix},
$$

which replaces the unavailable blocks $\mathbf X^\top\mathbf X/n$, $\widetilde{\mathbf X}^\top\widetilde{\mathbf X}/n$, $\mathbf X^\top\widetilde{\mathbf X}/n$ of the knockoff Lasso by their population values (the ridge term $c\mathbf I$ is for numerical stability). Set $W_j=|\hat\beta_j|-|\hat\beta_{j+p}|$.

**Lemma (swap equivariance).** For $\min_{\boldsymbol\beta}\frac12\boldsymbol\beta^\top\mathbf C\boldsymbol\beta-\mathbf d^\top\boldsymbol\beta+\lambda\|\boldsymbol\beta\|_1+\gamma\|\boldsymbol\beta\|_2^2$, let $\boldsymbol\Pi_S$ swap coordinates $j$ and $j+p$ for $j\in S\subseteq\{1,\dots,p\}$. If $\boldsymbol\Pi_S^\top\mathbf C\boldsymbol\Pi_S=\mathbf C$, then $\hat{\boldsymbol\beta}$ solves the problem with data $\mathbf d$ if and only if $\boldsymbol\Pi_S\hat{\boldsymbol\beta}$ solves it with data $\boldsymbol\Pi_S\mathbf d$.

**Corollary (FDR control).** The matrix $\mathbf C$ above is $S$-swap invariant for every $S$, so the pseudo-lasso statistic has the flip-sign property, and the pseudo-lasso GhostKnockoffs procedure with fixed $\lambda$ controls the FDR at level $q$ using summary statistics only.

## Expansion

Since $\widetilde{\mathbf X}^\top\mathbf Y=\mathbf P^\top\mathbf X^\top\mathbf Y+\mathbf V^{1/2}\mathbf E^\top\mathbf Y$ and, conditionally on $\mathbf Y$, $\mathbf E^\top\mathbf Y\sim\mathcal N(\mathbf 0,\|\mathbf Y\|_2^2\mathbf I)$ independently of $\mathbf X$, the identity follows; the rest is that the knockoff filter is a function of $\mathbf W$. The lemma is a change of variables $\boldsymbol\beta'=\boldsymbol\Pi_S^\top\boldsymbol\beta$: the quadratic form is invariant by assumption and both norms are permutation invariant. The pseudo-lasso solution is proportional to the scout estimator with known precision matrix, and objectives of the same form appear in summary-statistic fine-mapping and polygenic-score methods; plugging their output into this construction adds FDR guarantees they otherwise lack. Power, not validity, is what the population-covariance substitution costs.

## Depends on

- [Gram-matrix sufficiency for summary-statistic knockoffs](gram-matrix-sufficiency-for-summary-statistic-knockoffs.md)

## Sources

- Z. Chen, Z. He, B. B. Chu, J. Gu, "Controlled Variable Selection from Summary Statistics Only? A Solution via GhostKnockoffs and Penalized Regression" (2024), Section 4.2, Proposition 2, Lemma 1 and Corollary 2. <https://doi.org/10.48550/arXiv.2402.12724>
