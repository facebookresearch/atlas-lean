# MR-effect network and recovery of direct causal effects

**Model.** Let $Y=(Y_1,\dots,Y_T)^\top$ be traits and $Z=(Z_1,\dots,Z_S)^\top$ SNPs. The traits obey the linear structural equation model

$$Y=GY+\Gamma Z+\epsilon,$$

where $G\in\mathbb R^{T\times T}$ is the direct-effect network (zero diagonal: no self-loops; cycles allowed), $\Gamma\in\mathbb R^{T\times S}$ holds direct SNP effects, $\epsilon$ is an error vector (possibly correlated, representing confounding), and $I-G$ is invertible. Then

$$Y=W\Gamma Z+\xi,\qquad \mathbf B=W\Gamma,\quad W=(I-G)^{-1},\quad \xi=W\epsilon,$$

so the marginal (GWAS) effect of $Z_k$ on $Y_i$ is $\beta_{ik}=\sum_j w_{ij}\gamma_{jk}$.

**Theorem (MR effect).** If $Z_k$ is a valid instrument for $Y_j$ to $Y_i$ (for instance $\gamma_{jk}\ne0$ and $\gamma_{lk}=0$ for all $l\ne j$), then

$$\frac{\beta_{ik}}{\beta_{jk}}=\frac{w_{ij}}{w_{jj}}=:\theta_{ij},$$

independent of $k$. Consequently the MR-effect matrix $\Theta=(\theta_{ij})$ satisfies

$$\Theta=W\,\operatorname{Diag}(w)^{-1},\qquad w=(w_{11},\dots,w_{TT}).$$

**Corollary (recovery of $G$).** Because $G$ has zero diagonal, the diagonal of $\operatorname{Diag}(w)^{-1}\Theta^{-1}=I-G$ equals $1$, so $w_{jj}=(\Theta^{-1})_{jj}$ and

$$G=I-\big(\Theta\,\operatorname{Diag}(w)\big)^{-1}=I-\operatorname{Diag}(w)^{-1}\Theta^{-1}.$$

Plugging in a consistent estimate $\hat\Theta$ (from pairwise robust MR on GWAS summary statistics) gives $\hat G$, which under regularity conditions is consistent and asymptotically normal.

## Depends on

- [Ratio estimate of a single SNP](../ratio-estimate.md)

## Expansion

A valid instrument for $Y_j$ enters the system only through $Y_j$, so its total effect on every trait is $w_{\cdot j}\gamma_{jk}$ and the ratio cancels the instrument strength $\gamma_{jk}$; this is the usual Wald ratio, which in a network measures the total effect of $Y_j$ on $Y_i$ along all directed paths, normalized by the feedback factor $w_{jj}$ that cycles through $Y_j$ add to its own response. Since $\Theta$ is $W$ with rescaled columns and $G=I-W^{-1}$, the unknown scales are pinned down by the no-self-loop constraint, which turns pairwise total effects into direct effects even with feedback loops. In practice each $\theta_{ij}$ is estimated by a pleiotropy-robust MR method (constrained maximum likelihood) and uncertainty is propagated by parametric bootstrap of the GWAS $z$-score matrix.

## Sources

- Z. Lin, W. Pan, H. Xue, "MR2G: A novel framework for causal network inference using GWAS summary data", *PLoS Genetics* 22(5):e1012144 (2026), equations (5)–(7), Theorem 1, Algorithm 1, Theorem 2, <https://doi.org/10.1371/journal.pgen.1012144>, PMCID: PMC13210398.
