# Fixed-effects partitioned heritability is characterized by three axioms

**Setting.** Let a phenotype follow the linear model $y = \mathbf{z}^T\mathbf{u} + e$, where $\mathbf{z} \in \mathbb{R}^m$ is a random genotype vector with $\mathbb{E}\mathbf{z} = 0$ and $\operatorname{Var}(\mathbf{z}) = \Sigma$ (positive definite, encoding linkage disequilibrium), $\mathbf{u} \in \mathbb{R}^m$ is a fixed vector of SNP effects, and $e$ is independent noise with variance $\sigma_e^2$. The fixed-effects heritability is

$$h^2(\mathbf{u};\Sigma) = 1 - \frac{\mathbb{E}\,\operatorname{Var}(y \mid \mathbf{z})}{\operatorname{Var}(y)} = \frac{\mathbf{u}^T\Sigma\mathbf{u}}{\mathbf{u}^T\Sigma\mathbf{u} + \sigma_e^2}.$$

For a subset $\mathcal{S} \subseteq \{1,\dots,m\}$ of SNPs write $\Sigma_{\mathcal{S}^c \mid \mathcal{S}} = \Sigma_{\mathcal{S}^c\mathcal{S}^c} - \Sigma_{\mathcal{S}^c\mathcal{S}}\Sigma_{\mathcal{S}\mathcal{S}}^{-1}\Sigma_{\mathcal{S}\mathcal{S}^c}$ for the conditional (Schur-complement) covariance.

**Proposition.** Suppose the heritability attributable to $\mathcal{S}$, $h^2_{\mathcal{S}}(\mathbf{u};\Sigma)$, is a quadratic form in $\mathbf{u}$ (over the common denominator $\operatorname{Var}(y)$) satisfying

1. $0 \le h^2_{\mathcal{S}}(\mathbf{u};\Sigma) \le h^2(\mathbf{u};\Sigma)$ for all $\mathbf{u}$;
2. $h^2_{\mathcal{S}}(\mathbf{u};\Sigma) = h^2(\mathbf{u};\Sigma)$ if and only if $\mathbf{u}_{\mathcal{S}^c} = 0$;
3. $h^2_{\mathcal{S}}(\mathbf{u};\Sigma)$ does not depend on $\Sigma_{\mathcal{S}^c\mathcal{S}^c}$.

Then necessarily

$$h^2_{\mathcal{S}} = \frac{\mathbf{u}^T\Sigma\mathbf{u} - \mathbf{u}_{\mathcal{S}^c}^T\,\Sigma_{\mathcal{S}^c \mid \mathcal{S}}\,\mathbf{u}_{\mathcal{S}^c}}{\mathbf{u}^T\Sigma\mathbf{u} + \sigma_e^2}.$$

For Gaussian genotypes this equals $1 - \mathbb{E}\,\operatorname{Var}(y \mid \mathbf{z}_{\mathcal{S}})/\operatorname{Var}(y)$, the fraction of phenotypic variance explained by the SNPs in $\mathcal{S}$ including what they explain through LD with the other SNPs; and $h^2_{\{1,\dots,m\}} = h^2$.

## Expansion

Write $h^2_{\mathcal{S}} = \mathbf{u}^T M \mathbf{u}/\operatorname{Var}(y)$ for a symmetric $M$. Properties 1–2 force $\Sigma - M$ to be positive semidefinite with kernel exactly $\{\mathbf{u}_{\mathcal{S}^c} = 0\}$, so $\mathbf{u}^T(\Sigma - M)\mathbf{u}$ is a positive definite form in $\mathbf{u}_{\mathcal{S}^c}$ after eliminating $\mathbf{u}_{\mathcal{S}}$; property 3 then pins it to the Schur complement $\Sigma_{\mathcal{S}^c \mid \mathcal{S}}$. The definition is natural for the Mahalanobis genetic relationship matrix $K \propto Z\Sigma^{-1}Z^T$: with that kernel, random-effects heritability approximately equals fixed-effects heritability and does not depend on how causal variants are distributed relative to LD, whereas the usual Euclidean GRM $K \propto ZZ^T$ gives LD-dependent biases.

## Sources

- R. Ma and L. H. Dicker, "The Mahalanobis kernel for heritability estimation in genome-wide association studies: fixed-effects and random-effects methods", arXiv:1901.02936 (2019), Section 3 (fixed-effects heritability, Mahalanobis kernel, partitioned heritability and Proposition 1), <https://doi.org/10.48550/arXiv.1901.02936>.
