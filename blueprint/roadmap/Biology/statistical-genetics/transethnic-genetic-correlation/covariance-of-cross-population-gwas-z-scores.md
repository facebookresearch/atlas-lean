# Covariance of cross-population GWAS Z-scores under the infinitesimal model

Let study $p\in\{1,2\}$ have $N_p$ individuals genotyped at the same $M$ SNPs, with genotype matrix $X'_p$ standardised to mean $0$ and variance $1$ per SNP, rows drawn independently from a population with LD correlation matrix $\Sigma_p$, and standardised phenotype $Y_p=X'_p\beta_p+\varepsilon_p$. Assume

$$\begin{pmatrix}\beta_1\\\beta_2\end{pmatrix}\sim N\!\left(0,\frac1M\begin{pmatrix}h_1^2I_M&\rho_{gi}h_1h_2I_M\\\rho_{gi}h_1h_2I_M&h_2^2I_M\end{pmatrix}\right),\qquad \varepsilon_p\sim N\big(0,(1-h_p^2)I_{N_p}\big),$$

independently of genotypes and of each other across studies. Let $Z_p=X_p'^{\top}Y_p/\sqrt{N_p}$. Then $Z=(Z_1,Z_2)$ has mean $0$ and, under the moment approximations of the derivation, is asymptotically normal with covariance

$$\operatorname{Var}(Z)=\begin{pmatrix}\Sigma_1+\frac{N_1+1}{M}h_1^2\Sigma_1^2&\frac{\sqrt{N_1N_2}}{M}\rho_{gi}h_1h_2\,\Sigma_1\Sigma_2\\[2pt]\frac{\sqrt{N_1N_2}}{M}\rho_{gi}h_1h_2\,\Sigma_2\Sigma_1&\Sigma_2+\frac{N_2+1}{M}h_2^2\Sigma_2^2\end{pmatrix}.$$

If instead effects act on mean-centred genotypes with $\operatorname{Var}(\beta_p)=\frac{h_p^2}{\|\sigma_p^2\|_1}I_M$ and cross-covariance $\frac{\rho_{ge}h_1h_2}{\sqrt{\|\sigma_1^2\|_1\|\sigma_2^2\|_1}}I_M$, the substitution $\beta_p\to\sigma_p\beta_p$ gives

$$\operatorname{Var}(Z_p)=\Sigma_p+\frac{N_p+1}{\|\sigma_p^2\|_1}h_p^2\,\Sigma_pD_p^2\Sigma_p,\qquad \operatorname{Cov}(Z_1,Z_2)=\frac{\sqrt{N_1N_2}\,\rho_{ge}h_1h_2}{\sqrt{\|\sigma_1^2\|_1\|\sigma_2^2\|_1}}\,\Sigma_1D_1D_2\Sigma_2,$$

where $D_p=\mathrm{diag}(\sigma_p)$. Heritabilities and $\rho_{gi}$ or $\rho_{ge}$ are estimated by maximising the Gaussian likelihood $-\ln|C|-Z^\top C^{-1}Z$.

## Depends on

- [Genetic-effect and genetic-impact correlation](genetic-effect-and-genetic-impact-correlation.md)

## Expansion

Conditionally on $\beta$, $Z$ is approximately Gaussian, and the infinitesimal prior makes the unconditional law Gaussian, so only the first two moments are needed. The within-population term follows from $E[X_{1i}'^{\top}X'_1X_1'^{\top}X'_{1j}]\approx N_1Mr_{ij}+N_1(N_1+1)(\Sigma_1^2)_{ij}$ together with the residual term $(1-h_1^2)r_{ij}$. The cross term involves independent samples, so it factorises as $N_1N_2(\Sigma_1\Sigma_2)_{ij}$ times the effect covariance. In practice the method keeps only the diagonal of each block, down-weights SNPs in high LD, and approximates $(\Sigma_a\Sigma_b)_{ii}$ by sums of $r_{a,iw}r_{b,iw}$ over a window, as in LD-score regression.

## Sources

- B. C. Brown et al., "Transethnic Genetic-Correlation Estimates from Summary Statistics", Am. J. Hum. Genet. 99 (2016), 76–88, Equations (1)–(2) and Appendix A, Equations (A1)–(A4), <https://doi.org/10.1016/j.ajhg.2016.05.001>, PMCID PMC5005434.
