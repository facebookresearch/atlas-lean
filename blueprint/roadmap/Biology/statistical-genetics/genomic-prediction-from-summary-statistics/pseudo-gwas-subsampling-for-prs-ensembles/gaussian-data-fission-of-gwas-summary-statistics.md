# Gaussian data fission of GWAS summary statistics

**Model.** For population $k$ with $n_k$ individuals, standardized phenotype $y_k=X_k\beta_k+\epsilon_k$, $\epsilon_k\sim N(0,I_{n_k})$, and column-standardized genotypes $X_k$, the marginal GWAS estimates are

$$
\hat\beta_k=\frac{X_k^\top y_k}{n_k}\sim N\Bigl(D_k\beta_k,\ \frac{D_k}{n_k}\Bigr),\qquad D_k=\frac{X_k^\top X_k}{n_k}.
$$

**Data fission.** If $X\sim N(\mu,\Sigma)$ in $\mathbb R^d$, $Z\sim N(0,\Sigma)$ is drawn independently, and $\tau>0$, then $f(X)=X+\tau Z$ and $g(X)=X-\tau^{-1}Z$ are independent with $f(X)\sim N(\mu,(1+\tau^2)\Sigma)$ and $g(X)\sim N(\mu,(1+\tau^{-2})\Sigma)$.

**Pseudo-GWAS subsampling.** Applied to $\hat\beta_k$, with $G\sim N(0,I)$,

$$
\tilde\beta_k^{\rm train}=\hat\beta_k+\sqrt{\frac{n_{k,\rm tune}}{n_{k,\rm train}n_k}}\,D_k^{1/2}G,\qquad
\tilde\beta_k^{\rm tune}=\hat\beta_k-\sqrt{\frac{n_{k,\rm train}}{n_{k,\rm tune}n_k}}\,D_k^{1/2}G,
$$

where $n_{k,\rm train}=n_k/(1+\tau^2)$, $n_{k,\rm tune}=n_k\tau^2/(1+\tau^2)$ (so $\tau^2=n_{k,\rm tune}/n_{k,\rm train}$). These are independent and distributed as summary statistics of disjoint GWAS of sizes $n_{k,\rm train}$ and $n_{k,\rm tune}$: $N(D_k\beta_k,D_k/n_{k,\rm train})$ and $N(D_k\beta_k,D_k/n_{k,\rm tune})$.

**LD mismatch.** If the unknown $D_k$ is replaced by a reference $D_k^{\rm ref}$, the training and tuning residuals have cross-covariance $(D_k-D_k^{\rm ref})/n_k$ instead of $0$, so tuning on the second half partly re-uses training noise and overfits.

## Depends on

- [Marginal least-squares estimate of a marker effect](../marginal-estimate.md)

## Proof depends on

- [Covariances of linear functionals of a Gaussian vector](../../../../Probability/distributions/continuous/gaussian-conditioning/covariance-inner-of-map-eq.md)

## Expansion

Independence follows because $(f,g)$ is jointly Gaussian with $\operatorname{Cov}(X+\tau Z,X-\tau^{-1}Z)=\Sigma-\Sigma=0$. With the reference panel, the cross term becomes $D_k/n_k-D_k^{\rm ref}/n_k$; summed over millions of correlated SNPs, small LD differences accumulate into substantial residual correlation. Restricting to an LD-pruned SNP set (pairwise $r^2$ below a threshold in sliding windows) and setting $D_k\approx I$ makes the mismatch negligible, which is how the procedure is used in practice. The training-to-tuning ratio $3$ (that is $\tau^2=1/3$) with four repeats mimics fourfold Monte Carlo cross-validation.

## Sources

- Xu L, Dong Y, Zeng X, Bian Z, Zhou G, Guan L, Zhao H. MIXPRS enables multi-population and multi-method polygenic risk scores using summary statistics. *Nature Genetics* (2026). <https://doi.org/10.1038/s41588-026-02637-4>. PMCID: PMC13364660. Methods, Step 1 (Theorem 1 on data fission; ideal and practical pseudo-GWAS subsampling; LD pruning).
