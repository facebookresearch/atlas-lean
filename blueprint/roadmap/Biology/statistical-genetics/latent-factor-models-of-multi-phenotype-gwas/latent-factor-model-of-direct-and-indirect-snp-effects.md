# Latent-factor model of direct and indirect SNP effects

Let $Y\in\mathbb R^{N\times M}$ hold $M$ phenotypes (for example metabolite levels) of $N$ unrelated individuals and $X\in\mathbb R^{N\times S}$ their genotypes at $S$ SNPs. Assume $X$ has bounded, mean-zero, independent entries with identically distributed rows and $\operatorname{Var}(X_{is})\ge\epsilon>0$ (mean-centered genotypes, LD-pruned SNPs). The model is

$$Y=CL^\top+X\Delta+E,\qquad E\sim MN\bigl(0,I_N,\operatorname{diag}(\sigma_1^2,\dots,\sigma_M^2)\bigr),\qquad C=XG+\Xi,$$

with $K$ latent factors $C\in\mathbb R^{N\times K}$, rows of $\Xi$ independent with mean $0$ and covariance $\Psi$, factor loadings $L\in\mathbb R^{M\times K}$, SNP-on-factor effects $G\in\mathbb R^{S\times K}$, and direct effects $\Delta\in\mathbb R^{S\times M}$. The total genetic effect is

$$\mathbb E(Y\mid X)=X(GL^\top+\Delta),$$

so SNP $s$ acts on phenotype $m$ through the indirect (factor-mediated) effect $G_{s*}^\top L_{m*}$ and the direct effect $\Delta_{sm}$. The non-genetic phenotype covariance $L\Psi L^\top+\operatorname{diag}(\sigma_m^2)$ is low rank plus diagonal. The direct effects are sparse: $\Delta_{sm}\ne0$ with probability $\pi_{sm}$, $\max\pi_{sm}=o(1)$, and nonzero $\Delta_{sm}$ follow a finite normal scale mixture with standard deviations $O(N^{-1/2})$.

Only standardized marginal GWAS estimates $\hat B\in\mathbb R^{S\times M}$ and the diagonal $D=\operatorname{diag}(X_{*s}^\top X_{*s})$ are observed. Writing $\tilde G$ for the standardized SNP-on-factor effects, under the regularity conditions of the source there is a parametrization with $\mathbb E(S^{-1}\tilde G^\top\tilde G\mid G)=I_K$ and $M^{-1}L^\top L=\operatorname{diag}(\lambda_1,\dots,\lambda_K)$, $\lambda_1>\dots>\lambda_K>0$, in which the columns of $G$ and $L$ are identified up to sign; if in addition the factor effects are spread over many SNPs, each standardized effect $\tilde G_{sk}$ is bounded away from $0$ with high probability.

## Expansion

The model is a genetic analogue of a factor-analytic mediation model: shared pathways (latent factors) induce correlated SNP effects across phenotypes, and $\Delta$ captures the remaining idiosyncratic effects. Because $\hat B\approx D^{1/2}(GL^\top+\Delta)$ plus noise, the leading singular subspace of $\hat B$ carries the factor structure, which is what the summary-statistic estimators exploit. The normalization fixes the rotational non-identifiability of $GL^\top$ by orthonormalizing $G$ and diagonalizing $L^\top L$.

## Sources

- W. Huang, E. C. Hector, J. Cape and C. McKennan, "A statistical framework for GWAS of high dimensional phenotypes using summary statistics, with application to metabolite GWAS", arXiv preprint (2023), <https://doi.org/10.48550/arXiv.2303.10221>. Section 2 (model, Assumptions 2.1-2.2) and Proposition 2.1.
