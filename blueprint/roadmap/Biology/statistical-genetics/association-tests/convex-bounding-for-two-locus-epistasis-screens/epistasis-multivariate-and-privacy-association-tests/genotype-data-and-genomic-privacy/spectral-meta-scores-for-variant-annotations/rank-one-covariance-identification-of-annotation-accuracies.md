# Rank-one covariance identification of annotation accuracies

**Model.** Let $Z_i = (Z_{i1},\dots,Z_{ik})$, $i = 1,\dots,m$, be i.i.d. vectors of $k$ functional annotation scores of variants, standardized so that $\mathbb E[Z_{ij}] = 0$ and $\operatorname{Var}(Z_{ij}) = 1$. Let $C_i \in \{0,1\}$ be the unobserved functional status, $\pi = P(C_i = 1) \in (0,1)$, and $\mu_{jl} = \mathbb E[Z_{ij} \mid C_i = l]$. Each score is a two-component mixture $F_j = \pi F_{j1} + (1-\pi) F_{j0}$, so

$$\mu_{j1} = -\frac{1-\pi}{\pi}\,\mu_{j0}, \qquad \mu_{j1} - \mu_{j0} = -\frac{1}{\pi}\,\mu_{j0}.$$

**Covariance decomposition.** With $Q$ the covariance matrix of $Z_i$, $\Sigma_l$ the covariance given $C_i = l$, and $\mu_0 = (\mu_{10},\dots,\mu_{k0})$,

$$Q = \pi\,\Sigma_1 + (1-\pi)\,\Sigma_0 + R, \qquad R = \frac{1-\pi}{\pi}\,\mu_0^{\mathsf T}\mu_0 .$$

**Proposition (conditional independence).** If the scores are conditionally independent given $C_i$, then for $j_1 \neq j_2$

$$\operatorname{Cov}(Z_{ij_1}, Z_{ij_2}) = \frac{1-\pi}{\pi}\,\mu_{j_10}\,\mu_{j_20},$$

so the off-diagonal entries of $Q$ coincide with those of the rank-one matrix $R$, whose leading eigenvector is proportional to $\mu_0$, i.e. to the separation $|\mu_{j1} - \mu_{j0}|$ of each score.

**Lemma (blockwise identification).** Suppose the scores split into three or more disjoint exhaustive blocks such that scores in different blocks are conditionally independent given $C_i$ (scores within a block may be dependent). Writing $|q_{ij}| = e^{t_i} e^{t_j}$, the system

$$\log|q_{ij}| = t_i + t_j \qquad (i, j \text{ in different blocks})$$

has a unique solution $t_1,\dots,t_k$. Hence every entry of $R$, including within-block and diagonal entries $r_{ij} = e^{t_i + t_j}$ (up to sign), is identified from between-block covariances.

**Meta-score.** With $e = (e_1,\dots,e_k)$ the leading eigenvector of the estimated $\hat R$ (obtained by least squares on the sample covariances), the Eigen score of variant $i$ is

$$\mathrm{Eigen}(i) = Z_i e^{\mathsf T} = \sum_{j=1}^k e_j Z_{ij}.$$

If within-component variances are small relative to the means then $Q \approx R$, and the leading eigenvector of $Q$ itself (Eigen-PC) approximates $\mu_0$.

## Depends on

Its statement uses only the notions recalled above.

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

The decomposition is the law of total covariance applied to the two-component mixture; conditional independence kills the within-component covariances off the diagonal, leaving the between-component term $R$. For identification, taking $i \in B_1$, $j \in B_2$, $l \in B_3$ gives $t_i = \tfrac12(\log|q_{ij}| + \log|q_{il}| - \log|q_{jl}|)$, which fixes every $t_i$; with only two blocks the system is invariant under $t_i \mapsto t_i + c$ on one block and $t_j \mapsto t_j - c$ on the other, so three blocks are needed. Larger eigenvector entries flag more discriminative annotations, so they serve as weights in the linear meta-score.

## Sources

- I. Ionita-Laza, K. McCallum, B. Xu, J. D. Buxbaum, "A spectral approach integrating functional genomic annotations for coding and noncoding variants", Nature Genetics 48:214–220 (2016), Methods, Eqs (1)–(5), Lemma 1 and the meta-predictor definition, <https://doi.org/10.1038/ng.3477>, PMCID PMC4731313.
