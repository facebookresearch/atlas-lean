# Asymptotic normality of the HiGSS summary-statistic estimators

In the [latent-factor model of direct and indirect SNP effects](latent-factor-model-of-direct-and-indirect-snp-effects.md), let $\hat B\in\mathbb R^{S\times M}$ be the standardized GWAS estimates and $D=\operatorname{diag}(X_{*s}^\top X_{*s})$. With $\Gamma=\operatorname{diag}(\gamma_1,\dots,\gamma_K)$, $U$ and $V$ the top $K$ singular values and left and right singular vectors of $\hat B$, the HiGSS estimators are

$$\hat G=S^{1/2}U,\qquad\hat L=S^{-1/2}V\Gamma,\qquad\hat\Delta=\hat B-\hat G\hat L^\top,\qquad\hat\sigma_m^2=S^{-1}\sum_{s=1}^S\hat\Delta_{sm}^2.$$

**Theorem.** Under the model assumptions and the eigenvalue-separation conditions on $L$, as $N,M,S\to\infty$ there are signs $a_1,\dots,a_K\in\{-1,1\}$ such that, conditionally on $(G,L,\Delta,X)$ and for fixed finite sets of SNPs $\mathcal S$ and phenotypes $\mathcal M$:

1. the rows $\hat G_{s*}-D_{ss}^{1/2}\operatorname{diag}(a_1,\dots,a_K)G_{s*}$, $s\in\mathcal S$, are asymptotically independent standard $K$-variate normal;
2. $\hat\sigma_m^2=\sigma_m^2+o_P(1)$, and $\|\hat L_{m*}\|_2^{-1}\bigl(\hat G_{s*}^\top\hat L_{m*}-D_{ss}^{1/2}G_{s*}^\top L_{m*}\bigr)$ is asymptotically standard normal whenever $N^{1/2}\|L_{m*}\|_2\to\infty$, with a joint normal limit, up to a rotation $A$, for the rows of $\hat L$ scaled by $\{(N^{-1}+S^{-1})\hat\sigma_m^2\}^{-1/2}$;
3. the direct-effect estimates satisfy that $\hat\sigma_m^{-1}(\hat\Delta_{sm}-D_{ss}^{1/2}\Delta_{sm})$, $s\in\mathcal S$, $m\in\mathcal M$, are asymptotically independent standard normal.

When each factor is either pervasive ($\lambda_k\ge\eta>0$) or vanishing ($\lambda_k\to0$), the rotation relating $\hat L$ to $L$ is a sign matrix on the non-pervasive factors and within $O_P(N^{-1/2})$ of a sign matrix on the pervasive block.

These limits justify the HiGSS posterior $\mathcal N(\hat G_{s*};D_{ss}^{1/2}G_{s*},I_K)$, $\mathcal N(\hat L_{m*};L_{m*},(N^{-1}+S^{-1})\hat\sigma_m^2I_K)$ and $\mathcal N(\hat\Delta_{sm};D_{ss}^{1/2}\Delta_{sm},\hat\sigma_m^2)$ likelihood approximations, combined with priors (for example pathway-centric priors in metabolite GWAS) to infer shared and direct genetic effects from summary statistics alone.

## Depends on

- [Latent-factor model of direct and indirect SNP effects](latent-factor-model-of-direct-and-indirect-snp-effects.md)

## Expansion

The marginal estimates satisfy $\hat B\approx D^{1/2}(GL^\top+\Delta)+$ noise with independent standard normal-like entries after standardization. Sparsity and smallness of $\Delta$ make it a perturbation of the low-rank signal, so perturbation bounds for singular subspaces give $\hat G$ and $\hat L$ consistent up to sign, and a first-order expansion of the singular vectors yields the Gaussian limits. Residuals $\hat\Delta$ inherit the per-phenotype noise level $\sigma_m$, estimated by the residual mean square.

## Sources

- W. Huang, E. C. Hector, J. Cape and C. McKennan, "A statistical framework for GWAS of high dimensional phenotypes using summary statistics, with application to metabolite GWAS", arXiv preprint (2023), <https://doi.org/10.48550/arXiv.2303.10221>. Algorithm 1 (HiGSS), Assumption 3.1, Theorems 3.1-3.3 and Corollary 3.1.
