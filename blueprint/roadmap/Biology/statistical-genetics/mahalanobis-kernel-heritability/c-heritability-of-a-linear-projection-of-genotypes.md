# C-heritability of a linear projection of genotypes

**Setting.** In the fixed-effects linear model $y = \mathbf{z}^T\mathbf{u} + e$ with genotypes $\mathbf{z} \sim \mathcal{N}(0, \Sigma)$, independent noise $e \sim \mathcal{N}(0, \sigma_e^2)$ and fixed effects $\mathbf{u} \in \mathbb{R}^m$, let $C$ be a full-rank $m \times k$ matrix ($k \le m$), e.g. a projection onto a subset of SNPs or onto principal components. The heritability carried by the features $C^T\mathbf{z}$ is

$$h^2_C(\mathbf{u};\Sigma) = 1 - \frac{\mathbb{E}\,\operatorname{Var}(y \mid C^T\mathbf{z})}{\operatorname{Var}(y)}.$$

**Lemma.** Assume $\operatorname{Var}(y) = 1$. Then:

1. $h^2_C(\mathbf{u}; I) = \mathbf{u}^T C (C^TC)^{-1} C^T \mathbf{u}$, the squared length of the projection of $\mathbf{u}$ onto the column space of $C$;
2. $h^2_C(\mathbf{u};\Sigma) = h^2_{\Sigma^{1/2}C}(\Sigma^{1/2}\mathbf{u}; I)$, so correlated genotypes reduce to the white case after Mahalanobis whitening;
3. if $k = m$, then $h^2_C(\mathbf{u};\Sigma) = \mathbf{u}^T\Sigma\mathbf{u} = h^2$, the full fixed-effects heritability, for every invertible $C$;
4. for $\mathcal{S} \subseteq \{1,\dots,m\}$ and $\Pi_{\mathcal{S}}$ the coordinate projection onto $\mathcal{S}$, $h^2_{\Pi_{\mathcal{S}}}$ equals the partitioned heritability $h^2_{\mathcal{S}}$.

Moreover, with $W_C$ the whitened projected design, the Gaussian maximum-likelihood estimator built on the kernel $W_C W_C^T$ estimates $h^2_C$ through $\hat h^2_C = \hat\eta_C^2/(1 + \hat\eta_C^2)$.

## Depends on

- [Fixed-effects partitioned heritability is characterized by three axioms](fixed-effects-partitioned-heritability-is-characterized-by-three-axioms.md)

## Expansion

With white Gaussian $\mathbf{z}$, the conditional mean of $\mathbf{z}^T\mathbf{u}$ given $C^T\mathbf{z}$ is the projection $\mathbf{z}^T P_C \mathbf{u}$ with $P_C = C(C^TC)^{-1}C^T$, and the explained variance is $\|P_C\mathbf{u}\|^2$. For general $\Sigma$ write $\mathbf{z} = \Sigma^{1/2}\mathbf{w}$ with white $\mathbf{w}$, so that $\mathbf{z}^T\mathbf{u} = \mathbf{w}^T\Sigma^{1/2}\mathbf{u}$ and $C^T\mathbf{z} = (\Sigma^{1/2}C)^T\mathbf{w}$. An invertible $C$ loses no information, giving item 3. The lemma explains why the Mahalanobis kernel, which is the whitened Euclidean kernel, estimates the fixed-effects heritability consistently regardless of LD.

## Sources

- R. Ma and L. H. Dicker, "The Mahalanobis kernel for heritability estimation in genome-wide association studies: fixed-effects and random-effects methods", arXiv:1901.02936 (2019), Section 3 (definition of $C$-heritability, Lemma 1 and Proposition 2), <https://doi.org/10.48550/arXiv.1901.02936>.
